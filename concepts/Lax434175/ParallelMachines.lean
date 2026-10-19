import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Lax434175.Modules

/-!
---
title: Parallel machines
type: theorem
---
An instance on parallel machines has $n$ jobs, $m$ machines, and a
processing time $p_{ij}$ of job $j$ on machine $i$. A machine model on
parallel machines is a kernel whose instances are of this form, together
with the relation "at some time of schedule $\sigma$, job $j$ occupies
exactly the set $S$ of machines". Non-preemptive and preemptive scheduling
are two such models. A job may occupy several machines at once; the time it
then needs is its largest processing time on these machines.

The following fields restrict the instances of every machine model.

The machine-environment field:

- identical machines: the processing time of a job is the same on every
  machine;
- uniform machines: there are a length $q_j$ for every job and a positive
  speed $s_i$ for every machine with $p_{ij} \cdot s_i = q_j$;
- unrelated machines: no restriction.

Processing times are integral, so uniform machines are represented with the
time unit chosen fine enough that every quotient $q_j / s_i$ is an integer.

The processing-time field:

- unit: $p_{ij} = 1$;
- equal: there is a number $p$ with $p_{ij} = p$;
- one or two: $p_{ij} \in \{1, 2\}$;
- arbitrary: no restriction.

In the environment field each value is a special case of the next. Unit
processing times are a special case of equal ones and of one or two, and
every value of arbitrary ones.

**Theorem.** Over every machine model, the machine-environment and
processing-time fields are sound.
-/

namespace Lax434175.ParallelMachines
open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The processing time of a job on a machine. -/
  p : Fin jobs → Fin machines → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

/-- The time a job needs when it occupies a set of machines. -/
def duration (x : Inst) (j : Fin x.jobs) (S : Finset (Fin x.machines)) : ℕ :=
  S.sup (x.p j)

/-- A kernel on parallel machines. -/
structure Model where
  kernel : Kernel
  /-- The parallel-machine instance underlying an instance of the kernel. -/
  inst : kernel.Inst → Inst
  /-- The jobs of the kernel are those of the underlying instance. -/
  jobs_eq : ∀ x, kernel.jobs x = (inst x).jobs
  /-- At some time of the schedule the job occupies exactly this set of
  machines. -/
  uses : (x : kernel.Inst) → kernel.Sched x → Fin (inst x).jobs →
    Finset (Fin (inst x).machines) → Prop

inductive Environment
  | identical
  | uniform
  | unrelated

/-- The instances of a machine environment. -/
def Environment.holds : Environment → Inst → Prop
  | .identical, x => ∀ j i i', x.p j i = x.p j i'
  | .uniform, x => ∃ (q : Fin x.jobs → ℕ) (s : Fin x.machines → ℕ),
      ∀ j i, 0 < s i ∧ x.p j i * s i = q j
  | .unrelated, _ => True

/-- The position of an environment in the chain identical, uniform, unrelated. -/
def Environment.rank : Environment → ℕ
  | .identical => 0
  | .uniform => 1
  | .unrelated => 2

/-- The machine-environment field. -/
def environment (M : Model) : Module M.kernel :=
  Module.ofRestriction Environment (fun v x => v.holds (M.inst x))
    (fun v w => decide (v.rank ≤ w.rank))

inductive ProcessingTimes
  | unit
  | equal
  | oneOrTwo
  | arbitrary
  deriving DecidableEq

/-- The instances of a processing-time restriction. -/
def ProcessingTimes.holds : ProcessingTimes → Inst → Prop
  | .unit, x => ∀ j i, x.p j i = 1
  | .equal, x => ∃ p, ∀ j i, x.p j i = p
  | .oneOrTwo, x => ∀ j i, x.p j i = 1 ∨ x.p j i = 2
  | .arbitrary, _ => True

def ProcessingTimes.le : ProcessingTimes → ProcessingTimes → Bool
  | _, .arbitrary => true
  | .unit, _ => true
  | v, w => decide (v = w)

/-- The processing-time field. -/
def processingTimes (M : Model) : Module M.kernel :=
  Module.ofRestriction ProcessingTimes (fun v x => v.holds (M.inst x)) ProcessingTimes.le

/-- The number of machines, a parameter of every machine model. -/
def machines (M : Model) : M.kernel.Inst → ℕ := fun x => (M.inst x).machines

axiom environment_sound (M : Model) : (environment M).Sound

axiom processingTimes_sound (M : Model) : (processingTimes M).Sound

end Lax434175.ParallelMachines
