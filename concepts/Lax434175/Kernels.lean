import Mathlib.Data.NNRat.Defs

/-!
---
title: Scheduling kernels
type: definition
---
A scheduling kernel fixes what a schedule is. It consists of a type of
instances, each with a number of jobs, a type of schedules for every
instance, and the feasibility predicate that belongs to the machine model
itself (for instance, that a machine processes one job at a time). Every job
has a release date; problems without release dates are those in which all
release dates are $0$.

Every kernel reports, for each schedule and each job, a start time and a
completion time. Times are nonnegative rational numbers, since a preempted
job may be interrupted at any moment. Constraints and objectives are written against these two
accessors only, so that one definition of, say, release dates applies to
every kernel.
-/

namespace Lax434175.Kernels

/-- A machine model: instances, schedules, and the accessors through which
constraints and objectives read a schedule. -/
structure Kernel where
  /-- The instances of the machine model. -/
  Inst : Type
  /-- The number of jobs of an instance. -/
  jobs : Inst → ℕ
  /-- The release date of a job. -/
  release : (x : Inst) → Fin (jobs x) → ℕ
  /-- The schedules of an instance. -/
  Sched : Inst → Type
  /-- The feasibility conditions of the machine model itself. -/
  feasible : (x : Inst) → Sched x → Prop
  /-- The time at which a job starts. -/
  start : (x : Inst) → Sched x → Fin (jobs x) → NNRat
  /-- The time at which a job completes. -/
  completion : (x : Inst) → Sched x → Fin (jobs x) → NNRat

/-- In every schedule that is feasible for the kernel, every job starts no
later than it completes. -/
def Kernel.StartsBeforeCompletion (K : Kernel) : Prop :=
  ∀ x (σ : K.Sched x), K.feasible x σ → ∀ j, K.start x σ j ≤ K.completion x σ j

end Lax434175.Kernels
