# Control policies in Aeon

Four deterministic closed-loop environments, implemented in ordinary Aeon.
State datatypes, transitions, controllers, rollout loops, and fitness functions
live in the packaged `Control*.ae` libraries. There are **no new Python runtime
helpers**, Gymnasium dependencies, or external simulators. Only existing scalar
operations from `Math` cross the language boundary. Python is used for tests
and Aeon's existing interpreter/synthesizers.

Run the reference controllers:

```bash
python -m aeon examples/synthesis/control/reference.ae
```

This prints held-out losses in thermostat, cruise-control, CartPole, pendulum
order: approximately `71.716`, `232.905`, `2.162`, and `236.318`. Smaller is
better. These are sums over time, averaged over two initial states; they are
not comparable across environments. Reference controllers beat the off,
coast, always-left, and zero-torque baselines on both splits.

## Synthesis

```bash
python -m aeon -s gp --budget 30 examples/synthesis/control/thermostat.ae
python -m aeon -s gp --budget 30 examples/synthesis/control/cruise_control.ae
python -m aeon -s gp --budget 30 examples/synthesis/control/cartpole.ae
python -m aeon -s gp --budget 30 examples/synthesis/control/pendulum.ae
python -m aeon -s gp --budget 30 examples/synthesis/control/thermostat_free.ae
```

The first four tasks **tune controller parameters** in fixed, interpretable
templates. Integer holes have bounded refinement types; conversion/scaling to
Float is written in Aeon. GP fills each task's holes jointly, validates their
types, and minimizes the training rollout loss. `held_out_loss` evaluates the
resulting policy on held-out initial states over a longer horizon. No
held-out score is part of the optimization decorator. `random_search` also
supports these joint holes.

The synthesis CLI reports solutions and prints the completed program. To print
its held-out score, replace the holes in the original task with the reported
expressions and run that hole-free file with `python -m aeon file.ae`; `main`
prints `held_out_loss`.

`thermostat_free.ae` instead synthesizes a Boolean policy body from temperature
and the previous heater setting. It supplies `cold`/`hot` predicates and hides
the reference controller and rollout helpers at the hole through lexical
shadowing. It uses the ordinary Aeon grammar, not a dedicated controller DSL.
Short runs may produce poor constant policies; a filled, type-correct policy
does not imply successful control. The same distinction applies to tuned
parameters: these finite-horizon empirical objectives do not prove stability,
optimality, or correctness for other initial states.

In one local five-second GP smoke run per parameter task, completed policies
had held-out losses about `87.185`, `231.779`, `1.141`, and `236.306`, respectively.
Search progress depends on the budget and machine; these are observations,
not acceptance thresholds or promised solutions.

## Models and objectives

**Thermostat** (`ControlThermostat`): a toy room model, one minute per step,
`T' = T + 0.05*(outside - T) + 1.2*heater`, targeting 22 °C. Policies observe
temperature and the previous heater state, so they can express hysteresis.
Loss is squared temperature error plus `0.05` per heater-on step and `0.25`
per switch. Training uses 40 steps from `(15, off, outside=10)` and
`(28, on, outside=10)`; held-out uses 80 steps from `(18, off, outside=8)` and
`(26, on, outside=14)`. Reference thresholds are 21.5/22.5 °C. Synthesis chooses
integer low/high thresholds from 18–21 and 22–25 °C.

**Cruise control** (`ControlCruise`): a toy longitudinal vehicle with
`v' = max(0, v + 0.1*(3*action - 0.05*v - 9.81*grade))`, using seconds and m/s.
Action combines throttle/brake and is clipped to `[-1,1]`. The policy observes
speed error and its accumulated integral; the integral is clipped to `[-20,20]`.
This is a bounded integrator, not a detailed actuator or anti-windup model.
Loss is squared speed error plus `0.1*action²`. Training uses two 60-step
episodes `(speed,target,grade)=(14,20,0),(24,20,0.02)`; held-out uses 120 steps
from `(12,18,0.03),(25,22,-0.02)`, all starting with zero integral.
Reference PI gains are `kp=0.4, ki=0.1`; synthesis searches `kp=0..0.8` in 0.1
steps and `ki=0..0.2` in 0.05 steps.

**CartPole** (`ControlCartPole`): explicit Euler, 0.02 s per step, cart mass 1 kg,
pole mass 0.1 kg, half-length 0.5 m, gravity 9.8 m/s², Boolean left/right force
of −10/+10 N. Its equations follow the official
[Gymnasium CartPole source](https://github.com/Farama-Foundation/Gymnasium/blob/main/gymnasium/envs/classic_control/cartpole.py).
Failure is `abs(position)>2.4` m or `abs(angle)>12°`. This task uses a custom
loss `position² + 0.01*velocity² + 10*angle² + 0.01*angular_velocity²`, rather
than Gym's reward. The state-feedback template pushes right when
`position + velocity + angle_gain*angle + rate_gain*angular_velocity >= 0`.
Reference gains are 10/2; synthesis domains are 1–20/0–10. Training uses two
60-step states `(x,v,angle,rate)=(0,0,0.03,0),(0,0,-0.04,0.02)`; held-out uses
150 steps from `(0.1,0.05,0.02,-0.03),(-0.1,-0.04,-0.03,0.02)`.

**Pendulum** (`ControlPendulum`): torque-limited swing-up and upright balance,
with mass/length 1, gravity 10, timestep 0.05 s, torque in `[-2,2]`, and angular
speed clipped to `[-8,8]`. Semi-implicit Euler and the loss
`wrapped_angle² + 0.1*angular_velocity² + 0.001*applied_torque²` follow the
[Gymnasium pendulum source](https://github.com/Farama-Foundation/Gymnasium/blob/main/gymnasium/envs/classic_control/pendulum.py).
Angles are wrapped to `[-pi,pi)`; zero is upright. The reference combines
energy pumping away from upright with PD stabilization near upright. The
template tunes `kp=5..12`, `kd=1..5`, and energy gain `ke=1..3`; reference
values are 8/2/1. Training uses 80 steps from `(angle,rate)=(0.2,0),(pi,0)`;
held-out uses 160 steps from `(2.4,0.3),(-2.7,-0.2)`.

These are deterministic Aeon experiments using fixed starts, not Gym API
adapters or reproductions of a published evaluation protocol. The thermostat
and cruise plants are intentionally simple models.

## Reuse and failure behavior

Each environment exposes `mk`, state accessors, `step`, `invalid`, `reference`,
`episode`, `training`, and `held_out`. A policy is an ordinary curried Aeon
function; the pendulum interface, for example, is
`(angle:Float) -> (angular_velocity:Float) -> Float`.

```aeon
import Control;
import ControlPendulum;

def brake(theta:Float)(rate:Float):Float := 0.0 - 2.0 * rate;
def run(args:Int):Float :=
    Control.loss (ControlPendulum.episode 100 brake (ControlPendulum.mk 0.2 0.0));
```

`Control.rollout` accepts horizons from 0 through 500. Its result records loss,
the number of transitions executed, and failure. Invalid states are checked
before the horizon test, including the state reached by the final permitted
transition. Nonfinite costs/totals and invalid states receive a finite penalty
of at least one million; failed episodes stop immediately. Actions are
saturated in the plants, and continuous-action costs use the applied action.
Runtime errors or timeouts in a synthesized policy are rejected by Aeon's
existing synthesis evaluator. `step` is a raw transition; use `episode` for
termination and fitness handling.

The tests check known one-step numerical results, action/state limits, angle
wrapping, thermostat memory, zero/final-step termination, nonfinite loss,
reference-versus-baseline performance on both splits, real joint-candidate
fitness, and a seeded GP run:

```bash
pytest tests/control_policy_test.py tests/shared_import_test.py
```
