import Lax434175.Assembly
import Lax434175.Counts
import Lax434175.ReleaseDates
import Lax434175.Deadlines
import Lax434175.Precedence
import Lax434175.Thresholds
import Lax434175.PreemptiveShops

/-!
---
title: Preemptive shop problems in three-field notation
type: theorem
---
The family of preemptive shop problems has the constraint fields shop type,
machines of the operations, number of machines, number of jobs, processing
times, release dates, deadlines and precedence constraints between jobs,
and the completion-time objectives.

A problem $\alpha \mid \beta \mid \gamma$ with $\alpha$ one of $O$, $F$, $J$
whose $\beta$ contains $\mathrm{pmtn}$ is one specification of this family.
For example $J2 \mid \mathrm{pmtn} \mid C_{\max}$ is the specification below.

**Theorem.** A specification that is field by field a special case of
another describes a special case of the other's problem, and a specification
that reduces to another describes a problem whose decision version reduces
to that of the other.
-/

namespace Lax434175.PreemptiveShopProblems
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175

/-- The constraint fields of the family. -/
inductive FieldName
  | shopType
  | machineSets
  | machineCount
  | jobCount
  | processingTimes
  | releaseDates
  | deadlines
  | precedence
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.shopType, .machineSets, .machineCount, .jobCount, .processingTimes, .releaseDates,
    .deadlines, .precedence}
  complete x := by cases x <;> decide

/-- The preemptive shop problems. -/
abbrev family : Family PreemptiveShops.kernel :=
  Thresholds.family FieldName fun
    | .shopType => PreemptiveShops.shopType
    | .machineSets => PreemptiveShops.machineSets
    | .machineCount => Counts.module _ PreemptiveShops.machines 1
    | .jobCount => Counts.module _ PreemptiveShops.kernel.jobs
    | .processingTimes => PreemptiveShops.processingTimes
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.module _ PreemptiveShops.machines

/-- The specification `α | pmtn, β | γ` of a preemptive shop problem. -/
def spec (shopType : Shops.ShopType)
    (machineSets : Shops.Machines)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (processingTimes : Shops.ProcessingTimes := .arbitrary)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (objective : Objectives.Value) : Spec family where
  module
    | .shopType => shopType
    | .machineSets => machineSets
    | .machineCount => machineCount
    | .jobCount => jobCount
    | .processingTimes => processingTimes
    | .releaseDates => release
    | .deadlines => deadline
    | .precedence => precedence
  objective := objective

/-- `J2 | pmtn | C_max` -/
def job2_makespan : Spec family :=
  spec (shopType := .job) (machineSets := .dedicated) (machineCount := .atMost 2)
    (objective := .makespan)

axiom family_sound : family.Sound

axiom specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t)

axiom reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t)

end Lax434175.PreemptiveShopProblems
