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

## Discovering controller structure with ReGuS

`thermostat_structure.ae` and `pendulum_structure.ae` search for controller
programs containing actions, sequences, loops, and branches. Their holes have
the ordinary inductive type `ControlProgram`. The interpreter keeps the
program's position while executing its actions, so a two-phase program can
complete one phase and continue with another.

```bash
python -m aeon -s regus --budget 60 examples/synthesis/control/thermostat_structure.ae
python -m aeon -s regus --budget 120 examples/synthesis/control/pendulum_structure.ae

# Identical problem and objective, with another backend:
python -m aeon -s gp --budget 60 examples/synthesis/control/thermostat_structure.ae
python -m aeon -s random_search --budget 30 examples/synthesis/control/pendulum_structure.ae
```

Each problem file defines its actions, sensor predicates, abstract-state
encoding, training and unseen initial states, horizons, per-step cost, terminal
penalties, complexity penalty, and objective decorators. ReGuS has no knowledge
of pendulums, thermostats, these initial states, or their target values.
Switching `-s` preserves all these definitions. Backends need to support the
task's ADT and objective; a backend with no ADT/optimization support may reject
it. A short search can return an early-stopping controller with a poor score.

The standard objective is `@minimize_float(objective controller)`. The optional
`@cluster(feature controller)` supplies ReGuS's abstract execution observations.
`feature` returns a deferred `(ignored:Int) -> ControlObservation` function so
ordinary fitness-only backends do not collect traces. ReGuS invokes this
function inside its timed evaluation worker. No special reward decorator or
Python environment registration is needed.

Thermostat actions are one minute of heating off/on. Pendulum actions are
single steps of energy pumping or PD balance with a finite gain palette, all
defined in the problem file. The search chooses both these numerical variants
and their control-flow composition. A manually written pendulum program that
uses the same vocabulary is:

```aeon
ControlProgram.loop 0
    (ControlProgram.branch 1 (ControlProgram.action 3) (ControlProgram.action 0))
```

For this particular problem, sensor 0 is always true, sensor 1 means catchable
near upright, action 3 balances with gains 8/2, and action 0 pumps energy. The
backend reads only the vocabulary sizes and abstract traces; these meanings
are in the `.ae` file. The tests check that this program has the original
reference controller's training loss. It is an illustration, not a claimed
output of every search run.

### Shared execution interface

`ControlTask.run actions predicates horizon advance cost invalid sense abstract
initial program` executes a program without collecting a trace. `record` takes
the same arguments and collects one abstract pre/post-state event per action.
`ControlTask.score finish result` adds the problem's terminal loss; `report`
packages a recorded execution for `ControlObservation.snapshot`.

`abstract` encodes the Boolean sensors as a bitmask, with sensor zero in the
highest bit. It must agree with `sense`. This avoids reevaluating every sensor
for every event; the interpreter reuses the previous action's post-state mask.
Vocabulary bounds are 32 actions, 16 sensors, and 32 training starts; horizons
are 1–500 actions. Training observations and fitness use the same starts.
Held-out evaluation is defined separately in each problem file.

One action budget and one instruction budget are shared by the entire program,
including nested loops and procedures. Invalid actions/guards fail, invalid
states are checked after each action including the last, and a loop body that
makes no action progress fails immediately. `halt` returns early. The supplied
goals penalize unspent action budget, so halting cannot earn a zero-cost success.
The internal `gap` constructor suspends a partial program at a binary AST path;
its observed prefix cost guides search. It is hidden at the synthesis hole,
and ReGuS checks both syntax and the observation's closedness flag before
accepting a finished controller, including controllers using supplied skills.

### Algorithm and scope

The new backend implements a bounded adaptation of
[ReGuS, Cui et al., PLDI 2024](https://herowanzhu.github.io/PLDI_2024.pdf):

- High-level UCT search chooses loop/sequence skeletons. Completed skeletons
  each retain their own priority queue when revisited; their best completed
  program scores feed back into the high-level tree.
- Low-level search executes prefixes and expands the first reached gap.
  Abstract pre-state disagreements at an action site trigger conditional
  proposals. The known action stays on its original branch while the new
  branch is completed; matching observed post-states prioritize rejoining.
  Repair and ordinary completion queues receive alternating turns to prevent
  cheap incomplete prefixes from starving conditional repair.
- Earlier `ControlProgram` bindings are available as reusable procedures.
  Users can retain a program synthesized on an easier task as an ordinary Aeon
  definition for the next task. Task ordering and curriculum construction are
  explicit in the source.

Every completed candidate passes the shared type/refinement validator and is
ranked by the problem's declared objectives. A monotone score transform and
structural search cost affect scheduling; final selection uses the unchanged
objective vector and the shared Pareto archive.

This implementation evaluates all supplied training starts together and returns
the best accepted candidate within the budget. The paper's progressive
seed/threshold protocol, automatic cross-task curriculum scheduling, and full
abstract-contract branch-merging machinery are not reproduced. Conditional
repair uses empirical pre-state disagreements and post-state agreement, not
proved Hoare contracts. Numerical search is over the problem's finite action
palette. No published ReGuS performance or generalization result is claimed.

Default search bounds are 23 program nodes, 3 loops, 9 sketch nodes, and 10,000
states. `AEON_SEED` controls stochastic choices. The Python `Config` API exposes
these limits and the worker allowance: ReGuS requests at least five seconds
per candidate because fitness and trace collection share a worker. Other
backends retain their existing allowance. An in-flight evaluation or compiler
check can finish after the outer search budget expires.

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
