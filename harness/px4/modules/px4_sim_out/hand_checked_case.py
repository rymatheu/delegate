#!/usr/bin/env python3
"""Writes hand-checked-case.json for px4_sim_out, three ticks worked out from adapter.cpp:
tick 0: no actuator_motors message: every PWM is the initial 1000.
tick 1: controls (0.5, NaN, 1.25, -0.1): 1000 + 1000*0.5 = 1500; NaN is disarmed, 1000; 1.25 is
        clipped to 1, 2000; -0.1 is clipped to 0, 1000.
tick 2: no message: the PWMs of tick 1 are held (1500, 1000, 2000, 1000)."""
import json, os, struct
HERE = os.path.dirname(os.path.abspath(__file__))
def f(x): return '0x%08x' % struct.unpack('<I', struct.pack('<f', x))[0]
NAN = '0x7fc00000'
ins = [dict(actuator_motors_updated='false', actuator_motors_control_0=f(0.7), actuator_motors_control_1=f(0.7),
            actuator_motors_control_2=f(0.7), actuator_motors_control_3=f(0.7)),
       dict(actuator_motors_updated='true', actuator_motors_control_0=f(0.5), actuator_motors_control_1=NAN,
            actuator_motors_control_2=f(1.25), actuator_motors_control_3=f(-0.1)),
       dict(actuator_motors_updated='false', actuator_motors_control_0=f(0.9), actuator_motors_control_1=f(0.9),
            actuator_motors_control_2=f(0.9), actuator_motors_control_3=f(0.9))]
outs = [dict(pwm0='1000', pwm1='1000', pwm2='1000', pwm3='1000'),
        dict(pwm0='1500', pwm1='1000', pwm2='2000', pwm3='1000'),
        dict(pwm0='1500', pwm1='1000', pwm2='2000', pwm3='1000')]
json.dump({"module": "px4_sim_out", "code_hash": "(computed by hand)", "campaign": "none",
           "kind": "hand-checked", "clause": "", "case": 0, "step": 2, "note": __doc__.replace('\n', ' '),
           "params": {}, "inputs": ins, "outputs": outs}, open(os.path.join(HERE, 'hand-checked-case.json'), 'w'), indent=2)
