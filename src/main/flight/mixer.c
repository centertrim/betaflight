/*
 * This file is part of Cleanflight and Betaflight.
 *
 * Cleanflight and Betaflight are free software. You can redistribute
 * this software and/or modify this software under the terms of the
 * GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option)
 * any later version.
 *
 * Cleanflight and Betaflight are distributed in the hope that they
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied
 * warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this software.
 *
 * If not, see <http://www.gnu.org/licenses/>.
 */

#include <stdbool.h>
#include <stdint.h>
#include <math.h>

#include "platform.h"

#include "build/debug.h"

#include "common/axis.h"
#include "common/filter.h"
#include "common/maths.h"

#include "config/config.h"
#include "config/feature.h"

#include "drivers/dshot.h"
#include "drivers/io.h"
#include "drivers/motor.h"
#include "drivers/time.h"

#include "fc/controlrate_profile.h"
#include "fc/core.h"
#include "fc/rc.h"
#include "fc/rc_controls.h"
#include "fc/rc_modes.h"
#include "fc/runtime_config.h"

#include "flight/failsafe.h"
#include "flight/gps_rescue.h"
#include "flight/imu.h"
#include "flight/mixer_init.h"
#include "flight/mixer_tricopter.h"
#include "flight/pid.h"
#include "flight/rpm_filter.h"

#include "pg/rx.h"

#include "rx/rx.h"

#include "sensors/battery.h"
#include "sensors/gyro.h"

#include "mixer.h"

#define DYN_LPF_THROTTLE_STEPS           100
#define DYN_LPF_THROTTLE_UPDATE_DELAY_US 5000 // minimum of 5ms between updates

static FAST_DATA_ZERO_INIT float motorMixRange;

float FAST_DATA_ZERO_INIT motor[MAX_SUPPORTED_MOTORS];
float motor_disarmed[MAX_SUPPORTED_MOTORS];

static FAST_DATA_ZERO_INIT int throttleAngleCorrection;

float getMotorMixRange(void)
{
    return motorMixRange;
}

void writeMotors(void)
{
    motorWriteAll(motor);
}

static void writeAllMotors(int16_t mc)
{
    // Sends commands to all motors
    for (int i = 0; i < mixerRuntime.motorCount; i++) {
        motor[i] = mc;
    }
    writeMotors();
}

void stopMotors(void)
{
    writeAllMotors(mixerRuntime.disarmMotorOutput);
    delay(50); // give the timers and ESCs a chance to react.
}

//KBI Tuning Variables
// System Variable: 3d_minsyncspeed - Inital sync speed during reversal (1000 seems good for 3-inch quad)
// System Variable: 3d_minsyncspeedphasetwo - Phase two sync speed during reversal (5000 seems good for 3-inch quad)
// System Variable: 3d_reversalrampuppwr - 50 seems good for all quads tested to-date. Range is 5 to 100 percent
// System Variable: 3d_reversalRPMdifferential -  30 seems good for all quads. RPM differential is used to determine if motors are reversed when checking RPMs
// System Variable: 3d_stabilizeTimeMs - Motor stabilization time using deadband throttle after reversal sync is complete
// System Variable: 3d_pidResetTimeMs - PID reset time after reversal sync is complete
// System Variable: 3d_throttleStepDelay - Range 1 to 50.  Slows down throttle adjustments to allow motors to better synchronize


static FAST_DATA_ZERO_INIT float throttle = 0;
static FAST_DATA_ZERO_INIT float mixerThrottle = 0;
static FAST_DATA_ZERO_INIT float motorOutputMin;
static FAST_DATA_ZERO_INIT float motorRangeMin;
static FAST_DATA_ZERO_INIT float motorRangeMax;
static FAST_DATA_ZERO_INIT float motorOutputRange;
static FAST_DATA_ZERO_INIT int8_t motorOutputMixSign;

static FAST_DATA_ZERO_INIT int8_t prevMotorOutputMixSign = 1; //kbi

static bool reversalInProcess = false;  // kbi
static bool stabilizeTimeInProcess = false;  // kbi
static bool motordirectionchange[4];    // kbi
static bool motorsynccomplete[4];       // kbi

static int idlethrottle [4];            // kbi

static void calculateThrottleAndCurrentMotorEndpoints(timeUs_t currentTimeUs)
{

    const int minspeed = flight3DConfig()->minsyncspeed3d / 100 / 2 * motorConfig()->motorPoleCount; //kbi
    const int minspeedphasetwo = flight3DConfig()->minsyncspeedphasetwo3d / 100 / 2 * motorConfig()->motorPoleCount; //kbi
    static int syncspeed; //kbi
    const long unsigned int stabilizeTimeUs = flight3DConfig()->stabilizeTimeMs3d * 1000; //kbi
    const unsigned int pidResetTimeUs = flight3DConfig()->pidResetTimeMs3d * 1000; //kbi
    static uint16_t rcThrottlePrevious = 0;   // Store the last throttle direction for deadband transitions
    static timeUs_t reversalTimeUs = 0; // time when motors last reversed in 3D mode
    static float motorRangeMinIncrease = 0;
    static int motorMinRPM[4];          // kbi
    static float rcPreviousth = 1500; //kbi
    static bool syncphasetwo; //kbi

    float currentThrottleInputRange = 0;

    if (mixerRuntime.feature3dEnabled) {
        uint16_t rcCommand3dDeadBandLow;
        uint16_t rcCommand3dDeadBandHigh;

        if (!ARMING_FLAG(ARMED)) {
            rcThrottlePrevious = rxConfig()->midrc; // When disarmed set to mid_rc. It always results in positive direction after arming.
            prevMotorOutputMixSign = 1;    // Reset MixSign to follow previous throttle
        }

        if (IS_RC_MODE_ACTIVE(BOX3D) || flight3DConfig()->switched_mode3d) {
            // The min_check range is halved because the output throttle is scaled to 500us.
            // So by using half of min_check we maintain the same low-throttle deadband
            // stick travel as normal non-3D mode.
            const int mincheckOffset = (rxConfig()->mincheck - PWM_RANGE_MIN) / 2;
            rcCommand3dDeadBandLow = rxConfig()->midrc - mincheckOffset;
            rcCommand3dDeadBandHigh = rxConfig()->midrc + mincheckOffset;
        } else {
            rcCommand3dDeadBandLow = rxConfig()->midrc - flight3DConfig()->deadband3d_throttle;
            rcCommand3dDeadBandHigh = rxConfig()->midrc + flight3DConfig()->deadband3d_throttle;
        }

        rcPreviousth = rcPreviousth - (rcPreviousth - rcCommand[THROTTLE])/(flight3DConfig()->throttleStepDelay3d * 10); //kbi Step Throttle

        const float rcCommandThrottleRange3dLow = rcCommand3dDeadBandLow - PWM_RANGE_MIN;
        const float rcCommandThrottleRange3dHigh = PWM_RANGE_MAX - rcCommand3dDeadBandHigh;

        //Low Throttle
        if (rcPreviousth <= rcCommand3dDeadBandLow || isFlipOverAfterCrashActive()) {
            // INVERTED
            motorRangeMin = mixerRuntime.motorOutputLow;
            motorRangeMax = mixerRuntime.deadbandMotor3dLow;
#ifdef USE_DSHOT
            if (isMotorProtocolDshot()) {
                motorOutputMin = mixerRuntime.motorOutputLow;
                motorOutputRange = mixerRuntime.deadbandMotor3dLow - mixerRuntime.motorOutputLow;
            } else
#endif
            {
                motorOutputMin = mixerRuntime.deadbandMotor3dLow;
                motorOutputRange = mixerRuntime.deadbandMotor3dLow - mixerRuntime.deadbandMotor3dLow;
            }
            throttle = rcCommand3dDeadBandLow - rcPreviousth;
            rcThrottlePrevious = rcPreviousth;
            motorOutputMixSign = -1;
            currentThrottleInputRange = rcCommandThrottleRange3dLow;
        //High Throttle
        } else if (rcPreviousth >= rcCommand3dDeadBandHigh) {
            // NORMAL
            motorRangeMin = mixerRuntime.deadbandMotor3dHigh;
            motorRangeMax = mixerRuntime.motorOutputHigh;
            motorOutputMin = mixerRuntime.deadbandMotor3dHigh;
            motorOutputRange = mixerRuntime.motorOutputHigh - mixerRuntime.deadbandMotor3dHigh;
            rcThrottlePrevious = rcPreviousth;
            throttle = rcPreviousth - rcCommand3dDeadBandHigh;
            motorOutputMixSign = 1;
            currentThrottleInputRange = rcCommandThrottleRange3dHigh;
        // We are now within the deadband, but the last time we were outside the deadband we were below it in inverted mode.
        //   rcThrottlePrevious latches in our state the last time we were above or below the deadband.
        //   Throttle is cut anytime we are within the deadband.
        } else if ((rcThrottlePrevious <= rcCommand3dDeadBandLow &&
                !flight3DConfigMutable()->switched_mode3d) ||
                isMotorsReversed()) {
            // DEADBAND_FROM_INVERTED
            throttle = 0;
            motorOutputMixSign = -1;
            currentThrottleInputRange = rcCommandThrottleRange3dLow;
            motorRangeMin = mixerRuntime.motorOutputLow;
            motorRangeMax = mixerRuntime.deadbandMotor3dLow;
#ifdef USE_DSHOT
            if (isMotorProtocolDshot()) {
                motorOutputMin = mixerRuntime.motorOutputLow;
                motorOutputRange = mixerRuntime.deadbandMotor3dLow - mixerRuntime.motorOutputLow;
            } else
#endif
            {
                motorOutputMin = mixerRuntime.deadbandMotor3dLow;
                motorOutputRange = mixerRuntime.motorOutputLow - mixerRuntime.deadbandMotor3dLow;
            }
        // We are now within the deadband, but the last time we were outside the deadband we were above it in normal mode.
        //   Throttle is cut anytime we are within the deadband.
        } else {
            // DEADBAND_FROM_NORMAL
            throttle = 0;
            motorOutputMixSign = 1;
            currentThrottleInputRange = rcCommandThrottleRange3dHigh;
            motorRangeMin = mixerRuntime.deadbandMotor3dHigh;
            motorRangeMax = mixerRuntime.motorOutputHigh;
            motorOutputMin = mixerRuntime.deadbandMotor3dHigh;
            motorOutputRange = mixerRuntime.motorOutputHigh - mixerRuntime.deadbandMotor3dHigh;
        }

        // If motorOutputMixSign changed then Motor Reversal has been initiated
        if (motorOutputMixSign != prevMotorOutputMixSign) {
            prevMotorOutputMixSign = motorOutputMixSign;
            syncphasetwo = false;
            syncspeed = minspeed;
            for (int i = 0; i < mixerRuntime.motorCount; i++) {
               if (motorConfig()->dev.useDshotTelemetry){
                   // USE_RPM_FILTER will only be defined if USE_DSHOT and USE_DSHOT_TELEMETRY are defined
                   motorMinRPM[i] = getDshotTelemetry(i);
                   motordirectionchange[i] = false;
                   motorsynccomplete[i] = false;
                   reversalInProcess = stabilizeTimeInProcess = true;
                   reversalTimeUs = currentTimeUs + 500000; // Abort time 1/2-sec + stabilization time
                   idlethrottle[i] = 0;
               }
               else{
                   motorsynccomplete[i] = true;
                   reversalTimeUs = currentTimeUs;
                   syncphasetwo = true;
               }
            }
        }
        // RPM Sync reversal in process
        if ( reversalInProcess ){
            for (int i = 0; i < mixerRuntime.motorCount; i++) {
                 if ( !motorsynccomplete[i] ){
                     
                     // Monitor each motor for initial direction change
                     if ( !motordirectionchange[i] ){
                         // Follow RPM down and wait for direction change
                         if ( getDshotTelemetry(i) < motorMinRPM[i] ) {
                           motorMinRPM[i] = getDshotTelemetry(i);
                         }
                         // Finish when past differential, or abort after time-out.
                         if ( ((getDshotTelemetry(i) > flight3DConfig()->reversalRPMdifferential3d + motorMinRPM[i]) && (motorMinRPM[i] < syncspeed)) || currentTimeUs >= reversalTimeUs + 50000) {
                             motordirectionchange[i] = true;   //Motor Is Accelerating So Motor Has Reversed
                         }
                     }
                     
                     // Wait for each motor to sync at this phase rpm
                     if ( motordirectionchange[i] && getDshotTelemetry(i) > syncspeed) {
                             motorsynccomplete[i] = true;
                     }
                     
                     // All motors now syncronized
                     if ( motorsynccomplete[0] && motorsynccomplete[1] && motorsynccomplete[2] &&  motorsynccomplete[3]){
                         if (!syncphasetwo) {
                             // First phase sync complete, setup for phase 2 sync
                             syncphasetwo = true;
                             syncspeed = minspeedphasetwo;
                             motorsynccomplete[0] = motorsynccomplete[1] = motorsynccomplete[2] = motorsynccomplete[3] = false;
                         } else {
                            // Reversal Fully Complete, all motors have completed phase 2 sync
                            reversalTimeUs = currentTimeUs;
                            reversalInProcess = false;
                            pidResetIterm();  //kbi v10
                         }
                     }
                 // This motor achieved the sync rpm, track idle on it while waiting for the rest to catch up
                 } else if (getDshotTelemetry(i) < syncspeed) {
                     idlethrottle[i] = constrain(++idlethrottle[i],0,100); //,50,125);
                 } else {
                     idlethrottle[i] = constrain(--idlethrottle[i],0,100); //,50,125);
                 }
           }
        }

        if (stabilizeTimeInProcess){
            // Reset iTerm after stabilization time
            if ( currentTimeUs >= reversalTimeUs + stabilizeTimeUs ) {
                stabilizeTimeInProcess = false; //kbi v10
                pidResetIterm();  //kbi v10
            }
            // Hold throttle at zero until reversal is complete and stabilization time has passed, no matter if the actual throttle is now in the normal working range for this direction.
            //   Stock BF code only holds throttle = 0 while inside the deadband.
            //   If throttle is quickly moved through the deadband in the opposite direction then reversal will still change to the opposite direction.
            // Why can't all of this just be replaced with throttle = 0???
            else {
                throttle = 0;
                // throttle will snap to actual value after stabilization time has passed.... is this bad??  I guess it happens either way since we're driving the motors independently of throttle during reversal.
            }
        }

        // pidResetTime is different than stabilize time, because Stabilize time includes keeping throttle held to zero.
        //   Not sure why this would be useful / different though, since throttle without pid control is kinda nutty...
        if (currentTimeUs - reversalTimeUs < pidResetTimeUs ) {
            // keep iterm zero after motor reversal
            pidResetIterm();  //KBI V10
        }

    } else {
	// NORMAL mode (non-3D)
        throttle = rcCommand[THROTTLE] - PWM_RANGE_MIN + throttleAngleCorrection;
	currentThrottleInputRange = PWM_RANGE;
#if defined(USE_BATTERY_VOLTAGE_SAG_COMPENSATION)
        float motorRangeAttenuationFactor = 0;
        // reduce motorRangeMax when battery is full
        if (mixerRuntime.vbatSagCompensationFactor > 0.0f) {
            const uint16_t currentCellVoltage = getBatterySagCellVoltage();
            // batteryGoodness = 1 when voltage is above vbatFull, and 0 when voltage is below vbatLow
            float batteryGoodness = 1.0f - constrainf((mixerRuntime.vbatFull - currentCellVoltage) / mixerRuntime.vbatRangeToCompensate, 0.0f, 1.0f);
            motorRangeAttenuationFactor = (mixerRuntime.vbatRangeToCompensate / mixerRuntime.vbatFull) * batteryGoodness * mixerRuntime.vbatSagCompensationFactor;
            DEBUG_SET(DEBUG_BATTERY, 2, batteryGoodness * 100);
            DEBUG_SET(DEBUG_BATTERY, 3, motorRangeAttenuationFactor * 1000);
        }
        motorRangeMax = isFlipOverAfterCrashActive() ? mixerRuntime.motorOutputHigh : mixerRuntime.motorOutputHigh - motorRangeAttenuationFactor * (mixerRuntime.motorOutputHigh - mixerRuntime.motorOutputLow);
#else
        motorRangeMax = mixerRuntime.motorOutputHigh;
#endif

        motorRangeMin = mixerRuntime.motorOutputLow + motorRangeMinIncrease * (mixerRuntime.motorOutputHigh - mixerRuntime.motorOutputLow);
        motorOutputMin = motorRangeMin;
        motorOutputRange = motorRangeMax - motorRangeMin;
        motorOutputMixSign = 1;
    }

    throttle = constrainf(throttle / currentThrottleInputRange, 0.0f, 1.0f);
}

static void applyMixToMotors(float motorMix[MAX_SUPPORTED_MOTORS], motorMixer_t *activeMixer)
{
    // Now add in the desired throttle, but keep in a range that doesn't clip adjusted
    // roll/pitch/yaw. This could move throttle down, but also up for those low throttle flips.

    for (int i = 0; i < mixerRuntime.motorCount; i++) {
        float motorOutput = motorOutputMixSign * motorMix[i] + throttle * activeMixer[i].throttle;
#ifdef USE_THRUST_LINEARIZATION
        motorOutput = pidApplyThrustLinearization(motorOutput);
#endif
        motorOutput = motorOutputMin + motorOutputRange * motorOutput;

#ifdef USE_SERVOS
        if (mixerIsTricopter()) {
            motorOutput += mixerTricopterMotorCorrection(i);
        }
#endif
        if (failsafeIsActive()) {
#ifdef USE_DSHOT
            if (isMotorProtocolDshot()) {
                motorOutput = (motorOutput < motorRangeMin) ? mixerRuntime.disarmMotorOutput : motorOutput; // Prevent getting into special reserved range
            }
#endif
            motorOutput = constrainf(motorOutput, mixerRuntime.disarmMotorOutput, motorRangeMax);
        } else {
            // Override this motor output if sync is not complete during direction reversal
            if ( reversalInProcess ){
                // TODO: Probably only works for DSHOT?
                if ( !motorsynccomplete[i] ) { 
                    //KBI Boost throttle during reversal until sync speed is reached for this motor (idle + boost throttle)
                    motorOutput = motorOutputMin + (motorOutputRange * flight3DConfig()->reversalrampuppwr3d / 100.0f);
                } else {
                    // Sync complete for this motor, but waiting at tracking idle on the other motors to complete sync
                    // motorOutputMin includes digital_idle value already, so we'll range from 0% to 10% throttle on top of that
                    motorOutput = motorOutputMin + (motorOutputRange * idlethrottle[i] / 1000.0f);
                }
           }
           motorOutput = constrainf(motorOutput, motorRangeMin, motorRangeMax);
        }
        motor[i] = motorOutput;
    }

    // Disarmed mode
    if (!ARMING_FLAG(ARMED)) {
        for (int i = 0; i < mixerRuntime.motorCount; i++) {
            motor[i] = motor_disarmed[i];
        }
    }
}

static float applyThrottleLimit(float throttle)
{
    if (currentControlRateProfile->throttle_limit_percent < 100) {
        const float throttleLimitFactor = currentControlRateProfile->throttle_limit_percent / 100.0f;
        switch (currentControlRateProfile->throttle_limit_type) {
            case THROTTLE_LIMIT_TYPE_SCALE:
                return throttle * throttleLimitFactor;
            case THROTTLE_LIMIT_TYPE_CLIP:
                return MIN(throttle, throttleLimitFactor);
        }
    }

    return throttle;
}

static void applyMotorStop(void)
{
    for (int i = 0; i < mixerRuntime.motorCount; i++) {
        motor[i] = mixerRuntime.disarmMotorOutput;
    }
}

#ifdef USE_DYN_LPF
static void updateDynLpfCutoffs(timeUs_t currentTimeUs, float throttle)
{
    static timeUs_t lastDynLpfUpdateUs = 0;
    static int dynLpfPreviousQuantizedThrottle = -1;  // to allow an initial zero throttle to set the filter cutoff

    if (cmpTimeUs(currentTimeUs, lastDynLpfUpdateUs) >= DYN_LPF_THROTTLE_UPDATE_DELAY_US) {
        const int quantizedThrottle = lrintf(throttle * DYN_LPF_THROTTLE_STEPS); // quantize the throttle reduce the number of filter updates
        if (quantizedThrottle != dynLpfPreviousQuantizedThrottle) {
            // scale the quantized value back to the throttle range so the filter cutoff steps are repeatable
            const float dynLpfThrottle = (float)quantizedThrottle / DYN_LPF_THROTTLE_STEPS;
            dynLpfGyroUpdate(dynLpfThrottle);
            dynLpfDTermUpdate(dynLpfThrottle);
            dynLpfPreviousQuantizedThrottle = quantizedThrottle;
            lastDynLpfUpdateUs = currentTimeUs;
        }
    }
}
#endif

static void applyMixerAdjustmentLinear(float *motorMix, const bool airmodeEnabled) {
    const float motorMixNormalizationFactor = motorMixRange > 1.0f ? motorMixRange : 1.0f;
    const float motorMixDelta = 0.5f * motorMixRange;

    for (int i = 0; i < mixerRuntime.motorCount; ++i) {
        if (airmodeEnabled || throttle > 0.5f) {
            if (mixerConfig()->mixer_type == MIXER_LINEAR) {
                motorMix[i] = scaleRangef(throttle, 0.0f, 1.0f, motorMix[i] + motorMixDelta, motorMix[i] - motorMixDelta);
            } else {
                motorMix[i] = scaleRangef(throttle, 0.0f, 1.0f, motorMix[i] + ABS(motorMix[i]), motorMix[i] - ABS(motorMix[i]));
            }
        }
        motorMix[i] /= motorMixNormalizationFactor;
    }
}

static void applyMixerAdjustment(float *motorMix, const float motorMixMin, const float motorMixMax, const bool airmodeEnabled) {
#ifdef USE_AIRMODE_LPF
    const float unadjustedThrottle = throttle;
    throttle += pidGetAirmodeThrottleOffset();
    float airmodeThrottleChange = 0;
#endif

    if (motorMixRange > 1.0f) {
        for (int i = 0; i < mixerRuntime.motorCount; i++) {
            motorMix[i] /= motorMixRange;
        }
        // Get the maximum correction by setting offset to center when airmode enabled
        if (airmodeEnabled) {
            throttle = 0.5f;
        }
    } else {
        if (airmodeEnabled || throttle > 0.5f) {
            throttle = constrainf(throttle, -motorMixMin, 1.0f - motorMixMax);
#ifdef USE_AIRMODE_LPF
            airmodeThrottleChange = constrainf(unadjustedThrottle, -motorMixMin, 1.0f - motorMixMax) - unadjustedThrottle;
#endif
        }
    }

#ifdef USE_AIRMODE_LPF
    pidUpdateAirmodeLpf(airmodeThrottleChange);
#endif
}

FAST_CODE_NOINLINE void mixTable(timeUs_t currentTimeUs)
{
    // Find min and max throttle based on conditions. Throttle has to be known before mixing
    calculateThrottleAndCurrentMotorEndpoints(currentTimeUs);

    if (isFlipOverAfterCrashActive()) {
        //applyFlipOverAfterCrashModeToMotors();

        return;
    }

    const bool launchControlActive = isLaunchControlActive();

    motorMixer_t * activeMixer = &mixerRuntime.currentMixer[0];
#ifdef USE_LAUNCH_CONTROL
    if (launchControlActive && (currentPidProfile->launchControlMode == LAUNCH_CONTROL_MODE_PITCHONLY)) {
        activeMixer = &mixerRuntime.launchControlMixer[0];
    }
#endif

    // Calculate and Limit the PID sum
    const float scaledAxisPidRoll =
        constrainf(pidData[FD_ROLL].Sum, -currentPidProfile->pidSumLimit, currentPidProfile->pidSumLimit) / PID_MIXER_SCALING;
    const float scaledAxisPidPitch =
        constrainf(pidData[FD_PITCH].Sum, -currentPidProfile->pidSumLimit, currentPidProfile->pidSumLimit) / PID_MIXER_SCALING;

    uint16_t yawPidSumLimit = currentPidProfile->pidSumLimitYaw;

#ifdef USE_YAW_SPIN_RECOVERY
    const bool yawSpinDetected = gyroYawSpinDetected();
    if (yawSpinDetected) {
        yawPidSumLimit = PIDSUM_LIMIT_MAX;   // Set to the maximum limit during yaw spin recovery to prevent limiting motor authority
    }
#endif // USE_YAW_SPIN_RECOVERY

    float scaledAxisPidYaw =
        constrainf(pidData[FD_YAW].Sum, -yawPidSumLimit, yawPidSumLimit) / PID_MIXER_SCALING;

    if (!mixerConfig()->yaw_motors_reversed) {
        scaledAxisPidYaw = -scaledAxisPidYaw;
    }

    // Apply the throttle_limit_percent to scale or limit the throttle based on throttle_limit_type
    if (currentControlRateProfile->throttle_limit_type != THROTTLE_LIMIT_TYPE_OFF) {
        throttle = applyThrottleLimit(throttle);
    }

    // use scaled throttle, without dynamic idle throttle offset, as the input to antigravity
    pidUpdateAntiGravityThrottleFilter(throttle);

    // and for TPA
    pidUpdateTpaFactor(throttle);

#ifdef USE_DYN_LPF
    // keep the changes to dynamic lowpass clean, without unnecessary dynamic changes
    updateDynLpfCutoffs(currentTimeUs, throttle);
#endif

    // apply throttle boost when throttle moves quickly
#if defined(USE_THROTTLE_BOOST)
    if (throttleBoost > 0.0f) {
        const float throttleHpf = throttle - pt1FilterApply(&throttleLpf, throttle);
        throttle = constrainf(throttle + throttleBoost * throttleHpf, 0.0f, 1.0f);
    }
#endif

    // send throttle value to blackbox, including scaling and throttle boost, but not TL compensation, dyn idle or airmode 
    mixerThrottle = throttle;

#ifdef USE_DYN_IDLE
    // Set min throttle offset of 1% when stick is at zero and dynamic idle is active
    if (mixerRuntime.dynIdleMinRps > 0.0f) {
        throttle = MAX(throttle, 0.01f);
    }
#endif

#ifdef USE_THRUST_LINEARIZATION
    // reduce throttle to offset additional motor output
    throttle = pidCompensateThrustLinearization(throttle);
#endif

    // Find roll/pitch/yaw desired output
    // ??? Where is the optimal location for this code?
    float motorMix[MAX_SUPPORTED_MOTORS];
    float motorMixMax = 0, motorMixMin = 0;
    for (int i = 0; i < mixerRuntime.motorCount; i++) {

        float mix =
            scaledAxisPidRoll  * activeMixer[i].roll +
            scaledAxisPidPitch * activeMixer[i].pitch +
            scaledAxisPidYaw   * activeMixer[i].yaw;

        if (mix > motorMixMax) {
            motorMixMax = mix;
        } else if (mix < motorMixMin) {
            motorMixMin = mix;
        }
        motorMix[i] = mix;
    }

    //  The following fixed throttle values will not be shown in the blackbox log
    // ?? Should they be influenced by airmode?  If not, should go after the apply airmode code.
    const bool airmodeEnabled = airmodeIsEnabled() || launchControlActive;
#ifdef USE_YAW_SPIN_RECOVERY
    // 50% throttle provides the maximum authority for yaw recovery when airmode is not active.
    // When airmode is active the throttle setting doesn't impact recovery authority.
    if (yawSpinDetected && !airmodeEnabled) {
        throttle = 0.5f;
    }
#endif // USE_YAW_SPIN_RECOVERY

#ifdef USE_LAUNCH_CONTROL
    // While launch control is active keep the throttle at minimum.
    // Once the pilot triggers the launch throttle control will be reactivated.
    if (launchControlActive) {
        throttle = 0.0f;
    }
#endif

#ifdef USE_GPS_RESCUE
    // If gps rescue is active then override the throttle. This prevents things
    // like throttle boost or throttle limit from negatively affecting the throttle.
    if (FLIGHT_MODE(GPS_RESCUE_MODE)) {
        throttle = gpsRescueGetThrottle();
    }
#endif

    motorMixRange = motorMixMax - motorMixMin;
    if (mixerConfig()->mixer_type > MIXER_LEGACY) {
        applyMixerAdjustmentLinear(motorMix, airmodeEnabled);
    } else {
        applyMixerAdjustment(motorMix, motorMixMin, motorMixMax, airmodeEnabled);
    }

    if (featureIsEnabled(FEATURE_MOTOR_STOP)
        && ARMING_FLAG(ARMED)
        && !mixerRuntime.feature3dEnabled
        && !airmodeEnabled
        && !FLIGHT_MODE(GPS_RESCUE_MODE)   // disable motor_stop while GPS Rescue is active
        && (rcData[THROTTLE] < rxConfig()->mincheck)) {
        // motor_stop handling
        applyMotorStop();
    } else {
        // Apply the mix to motor endpoints
        applyMixToMotors(motorMix, activeMixer);
    }
}

void mixerSetThrottleAngleCorrection(int correctionValue)
{
    throttleAngleCorrection = correctionValue;
}

float mixerGetThrottle(void)
{
    return mixerThrottle;
}
