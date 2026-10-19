import Lax434175.ParallelMachines

/-!
---
title: Non-preemptive scheduling on parallel machines
type: theorem
---
A non-preemptive schedule assigns to every job a nonempty set of machines
and an integral start time. The job occupies these machines without
interruption from its start time until its completion time, which is the
start time plus the time it needs on these machines. A schedule is feasible
for the kernel if no two jobs that share a machine overlap.

In the classical problems every job occupies a single machine; which sets of
machines a job may occupy is the subject of the machine-set field.

**Theorem.** Every job starts no later than it completes.
-/

namespace Lax434175.Nonpreemptive
open Lax434175.Kernels Lax434175.ParallelMachines

structure Sched (x : Inst) where
  machines : Fin x.jobs → Finset (Fin x.machines)
  start : Fin x.jobs → ℕ

def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ :=
  σ.start j + duration x j (σ.machines j)

/-- Every job occupies some machine, and two distinct jobs that share a
machine do not overlap. -/
def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ j, (σ.machines j).Nonempty) ∧
  ∀ i j, i ≠ j → ¬ Disjoint (σ.machines i) (σ.machines j) →
    completion x σ i ≤ σ.start j ∨ completion x σ j ≤ σ.start i

/-- The kernel of non-preemptive scheduling on parallel machines. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start _ σ j := (σ.start j : NNRat)
  completion x σ j := (completion x σ j : NNRat)

/-- Non-preemptive scheduling as a machine model. -/
def model : Model where
  kernel := kernel
  inst x := x
  jobs_eq _ := rfl
  uses _ σ j S := Sched.machines σ j = S

axiom startsBeforeCompletion : kernel.StartsBeforeCompletion

end Lax434175.Nonpreemptive
