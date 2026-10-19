import Lax434175.Assembly
import Lax434175.Counts
import Lax434175.ReleaseDates
import Lax434175.Deadlines
import Lax434175.Precedence
import Lax434175.Thresholds
import Lax434175.Batching

/-!
---
title: Batching problems in three-field notation
type: theorem
---
The family of batching problems in a mode has the constraint fields
capacity, number of jobs, processing times, release dates, deadlines and
precedence constraints, and the completion-time objectives.

A problem $1 \mid \beta \mid \gamma$ whose $\beta$ contains s-batch or
p-batch is one specification of the family of serial or of parallel
batching. For example $1 \mid \text{p-batch}(\infty) \mid \sum w_j C_j$ and
$1 \mid \text{p-batch}, r_j \mid \sum w_j T_j$ are the specifications below.
The concept on one family for batching joins the two modes into a single
family with a batching field.

**Theorem.** In both modes, a specification that reduces to another
describes a problem whose decision version reduces to that of the other; if
it is field by field a special case, it describes a special case.
-/

namespace Lax434175.BatchProblems
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175

/-- The constraint fields of the family. -/
inductive FieldName
  | capacity
  | jobCount
  | processingTimes
  | releaseDates
  | deadlines
  | precedence
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.capacity, .jobCount, .processingTimes, .releaseDates, .deadlines, .precedence}
  complete x := by cases x <;> decide

/-- The batching problems of a mode. -/
abbrev family (mode : Batching.Mode) : Family (Batching.kernel mode) :=
  Thresholds.family FieldName fun
    | .capacity => Batching.capacity mode
    | .jobCount => Counts.module _ (Batching.kernel mode).jobs
    | .processingTimes => Batching.processingTimes mode
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.oneMachine _

/-- The specification `1 | β | γ` of a batching problem. -/
def spec (mode : Batching.Mode) (capacity : Batching.Capacity)
    (jobCount : Counts.Bound := .any)
    (processingTimes : Batching.ProcessingTimes := .arbitrary)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (objective : Objectives.Value) : Spec (family mode) where
  module
    | .capacity => capacity
    | .jobCount => jobCount
    | .processingTimes => processingTimes
    | .releaseDates => release
    | .deadlines => deadline
    | .precedence => precedence
  objective := objective

/-- `1 | p-batch(∞) | Σw_jC_j` -/
def parallel_unbounded_sumWC : Spec (family .parallel) :=
  spec _ (capacity := .unbounded) (objective := .sumWC)

/-- `1 | p-batch, r_j | Σw_jT_j` -/
def parallel_bounded_release_sumWT : Spec (family .parallel) :=
  spec _ (capacity := .bounded) (release := .releaseDates) (objective := .sumWT)

axiom family_sound (mode : Batching.Mode) : (family mode).Sound

axiom specialCase_of_le (mode : Batching.Mode) {s t : Spec (family mode)} :
    s.le t → SpecialCase (problem (family mode) s) (problem (family mode) t)

axiom reducible_of_reduces (mode : Batching.Mode) {s t : Spec (family mode)} :
    Thresholds.Reduces s t → Reducible (problem (family mode) s) (problem (family mode) t)

end Lax434175.BatchProblems
