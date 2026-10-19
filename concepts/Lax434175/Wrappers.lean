import Mathlib.Data.Set.Card
import Lax434175.OperationsFamily

/-!
---
title: At most k scheduled jobs, and prescribed machine loads
type: definition
---
Two problems built on a problem $s$ of the family with operations, as used for
interval scheduling with eligible machine sets (lax-767944).

A job is *kept* by a schedule if it is on time, for an objective that counts
late jobs, or just in time, for one that counts jobs not just in time; for the
other objectives no job is kept.

**At most $k$ scheduled jobs.** An instance is an instance $x$ of $s$ together
with a number $k$. A schedule is a schedule of $x$ together with a set $S$ of
at most $k$ jobs, the jobs it schedules; it is feasible if the schedule is
feasible for $s$. Its cost is the weight of the jobs that are not in $S$ or not
kept, so that a cost of at most $D$ says that some schedule of at most $k$ jobs
keeps weight at least $W - D$, with $W$ the total weight. This is the weighted
question parameterized by the number $k$ of scheduled jobs: a schedule of at
most $k$ jobs and weight at least a target.

**Prescribed machine loads.** An instance is an instance $x$ of $s$ together
with a number $q_i$ for every machine $i$. A schedule is feasible if it is
feasible for $s$ and every machine $i$ runs exactly $q_i$ jobs, a job running
on a machine if a piece of one of its operations occupies it. The cost is the
cost in $s$; with the threshold $0$ and an objective that counts jobs not just
in time, the question is whether all jobs can be scheduled with these loads
(Das, Opler and Valla).
-/

namespace Lax434175.Wrappers
open Lax434175 Lax434175.Problems Lax434175.Assembly

variable (s : Spec OperationsFamily.family)

/-- The weight of a job. -/
def weight (x : Inst OperationsFamily.family s) (j : Fin x.base.jobs) : ℕ :=
  Objectives.weight (K := Operations.kernel) s.objective x.objectiveData j

/-- The due date of a job. -/
def due (x : Inst OperationsFamily.family s) (j : Fin x.base.jobs) : ℕ :=
  Objectives.dueDate (K := Operations.kernel) s.objective x.objectiveData j

/-- The job is kept: on time for an objective counting late jobs, just in
time for one counting jobs not just in time, and never otherwise. -/
def Kept (x : Inst OperationsFamily.family s) (σ : Operations.Sched x.base)
    (j : Fin x.base.jobs) : Prop :=
  match Objectives.kind s.objective with
  | .late => Operations.kernel.completion x.base σ j ≤ (due s x j : NNRat)
  | .notJustInTime => Operations.kernel.completion x.base σ j = (due s x j : NNRat)
  | _ => False

open Classical in
/-- At most `k` scheduled jobs: the instance carries `k`, a schedule names the
at most `k` jobs it schedules, and the cost is the weight of the jobs not
scheduled or not kept. -/
noncomputable def atMostScheduled : Problem where
  Inst := Inst OperationsFamily.family s × ℕ
  Sched x := Operations.Sched x.1.base × Finset (Fin x.1.base.jobs)
  feasible x σ := (problem _ s).feasible x.1 σ.1 ∧ σ.2.card ≤ x.2
  cost x σ := ∑ j, (weight s x.1 j : ℚ) * if j ∈ σ.2 ∧ Kept s x.1 σ.1 j then 0 else 1

/-- The jobs that run on a machine. -/
def jobsOn (x : Inst OperationsFamily.family s) (σ : Operations.Sched x.base)
    (i : Fin x.base.machines) : Set (Fin x.base.jobs) :=
  {j | ∃ k, Operations.Occupies σ ⟨j, k⟩ i}

/-- Prescribed machine loads: the instance carries a number of jobs for every
machine, and a feasible schedule runs exactly that many jobs on every machine. -/
def prescribedLoads : Problem where
  Inst := (x : Inst OperationsFamily.family s) × (Fin x.base.machines → ℕ)
  Sched x := Operations.Sched x.1.base
  feasible x σ := (problem _ s).feasible x.1 σ ∧
    ∀ i, Set.ncard (jobsOn s x.1 σ i) = x.2 i
  cost x σ := (problem _ s).cost x.1 σ

end Lax434175.Wrappers
