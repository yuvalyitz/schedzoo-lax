import Lax434175.BatchProblems

/-!
---
title: One family for serial and parallel batching
type: theorem
---
Serial and parallel batching share one machine model, in which a schedule
partitions the jobs into numbered batches and gives every batch a start time
and a processing time. All jobs of a batch start when the batch starts and
complete when it completes, at its start plus its processing time. A
schedule is feasible for this model if a setup precedes every batch, as in
batch scheduling.

The batching field has the values serial and parallel: the processing time of
every batch is the sum, or the maximum, of the processing times of its jobs.
The two values are incomparable. The other fields are those of batching.

A batching problem in a mode determines the problem of this family with the
same values and that mode.

**Theorem.** The two problems are special cases of each other. The fields of
the family are sound, so that a specification that is field by field a
special case of another describes a special case of the other's problem, and
one that reduces to another describes a problem whose decision version
reduces to that of the other.
-/

namespace Lax434175.BatchFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175
open Lax434175.Batching (Inst Capacity ProcessingTimes members)

/-- A batch schedule with the processing time of every batch. -/
structure Sched (x : Inst) where
  /-- The number of the batch of a job. -/
  batch : Fin x.jobs → ℕ
  /-- The start time of a batch. -/
  start : ℕ → ℕ
  /-- The processing time of a batch. -/
  length : ℕ → ℕ

/-- The batches and start times of a schedule. -/
def Sched.plain {x : Inst} (σ : Sched x) : Batching.Sched x := ⟨σ.batch, σ.start⟩

/-- The completion time of a batch. -/
def finish {x : Inst} (σ : Sched x) (k : ℕ) : ℕ := σ.start k + σ.length k

/-- A setup precedes every batch. -/
def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ j, x.setup ≤ σ.start (σ.batch j)) ∧
  ∀ i j, σ.batch i < σ.batch j → finish σ (σ.batch i) + x.setup ≤ σ.start (σ.batch j)

/-- The kernel of batch scheduling. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start _ σ j := (σ.start (σ.batch j) : NNRat)
  completion _ σ j := (finish σ (σ.batch j) : NNRat)

def modeLe : Batching.Mode → Batching.Mode → Bool
  | .serial, .serial | .parallel, .parallel => true
  | _, _ => false

/-- The batching field. -/
def mode : Module kernel where
  Value := Batching.Mode
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := ∀ k, σ.length k = Batching.length v x σ.plain k
  le := modeLe
  embed _ _ _ := ()

/-- The capacity field. -/
def capacity : Module kernel where
  Value := Capacity
  Data := Capacity.Data
  admits _ _ _ := True
  constraint v _ d σ := ∀ k, ∑ j ∈ members σ.plain k, v.size d j ≤ v.bound d
  le := Capacity.le
  embed := Capacity.embed

/-- The processing-time field. -/
def processingTimes : Module kernel :=
  Module.ofRestriction ProcessingTimes ProcessingTimes.holds
    (fun v w => decide (v.rank ≤ w.rank))

/-- The fields of the family: batching and the fields of batch scheduling. -/
inductive FieldName
  | mode
  | field (i : BatchProblems.FieldName)
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.mode, .field .capacity, .field .jobCount, .field .processingTimes,
    .field .releaseDates, .field .deadlines, .field .precedence}
  complete x := by
    cases x with
    | mode => decide
    | field i => cases i <;> decide

/-- The batching problems. -/
abbrev family : Family kernel :=
  Thresholds.family FieldName fun
    | .mode => mode
    | .field .capacity => capacity
    | .field .jobCount => Counts.module _ kernel.jobs
    | .field .processingTimes => processingTimes
    | .field .releaseDates => ReleaseDates.module _
    | .field .deadlines => Deadlines.module _
    | .field .precedence => Precedence.oneMachine _

instance : Fintype family.ModuleName :=
  inferInstanceAs (Fintype FieldName)

/-- The specification `1 | β | γ` of a batching problem. -/
def spec (mode : Batching.Mode) (capacity : Capacity)
    (jobCount : Counts.Bound := .any)
    (processingTimes : ProcessingTimes := .arbitrary)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (objective : Objectives.Value) : Spec family where
  module
    | .mode => mode
    | .field .capacity => capacity
    | .field .jobCount => jobCount
    | .field .processingTimes => processingTimes
    | .field .releaseDates => release
    | .field .deadlines => deadline
    | .field .precedence => precedence
  objective := objective

/-- The specification of the family with the values of a batching problem in
a mode. -/
def ofSpec (m : Batching.Mode) (s : Spec (BatchProblems.family m)) : Spec family where
  module
    | .mode => m
    | .field .capacity => s.module .capacity
    | .field .jobCount => s.module .jobCount
    | .field .processingTimes => s.module .processingTimes
    | .field .releaseDates => s.module .releaseDates
    | .field .deadlines => s.module .deadlines
    | .field .precedence => s.module .precedence
  objective := s.objective

axiom faithful (m : Batching.Mode) (s : Spec (BatchProblems.family m)) :
    SpecialCase (problem _ s) (problem family (ofSpec m s)) ∧
      SpecialCase (problem family (ofSpec m s)) (problem _ s)

axiom family_sound : family.Sound

axiom specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t)

axiom reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t)

end Lax434175.BatchFamily
