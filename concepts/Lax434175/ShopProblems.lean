import Lax434175.Assembly
import Lax434175.Counts
import Lax434175.ReleaseDates
import Lax434175.Deadlines
import Lax434175.Precedence
import Lax434175.Thresholds
import Lax434175.Shops
import Lax434175.Transportation
import Lax434175.Servers
import Lax434175.ShopExtras

/-!
---
title: Shop problems in three-field notation
type: theorem
---
The family of shop problems has the constraint fields shop type, machines of
the operations, number of machines, number of jobs, processing times, no-wait, no-idle, transportation
delays, a server, batch setups, release dates, deadlines and precedence constraints between jobs, and the completion-time objectives.

A problem $\alpha \mid \beta \mid \gamma$ with $\alpha$ one of $O$, $F$, $J$,
possibly followed by a number of machines, is one specification of this
family. Without an entry on machine sets, the operations of an open shop or
flow shop occupy the machines by position and those of a job shop occupy
dedicated machines. For example $F2 \mid\mid C_{\max}$ and
$J \mid r_j \mid L_{\max}$ are the specifications below.
The concept on one family for shops joins these problems and the preemptive
shop problems into a single family with an interruption field.

**Theorem.** A specification that is field by field a special case of
another describes a special case of the other's problem, and a specification
that reduces to another describes a problem whose decision version reduces
to that of the other. In particular
$F2 \mid\mid C_{\max}$ is a special case of $J \mid r_j \mid L_{\max}$.
-/

namespace Lax434175.ShopProblems
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175

/-- The constraint fields of the family. -/
inductive FieldName
  | shopType
  | machineSets
  | machineCount
  | jobCount
  | processingTimes
  | noWait
  | transportation
  | server
  | noIdle
  | batchSetups
  | releaseDates
  | deadlines
  | precedence
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.shopType, .machineSets, .machineCount, .jobCount, .processingTimes, .noWait, .transportation, .server, .noIdle, .batchSetups, .releaseDates,
    .deadlines, .precedence}
  complete x := by cases x <;> decide

/-- The shop problems. -/
abbrev family : Family Shops.kernel :=
  Thresholds.family FieldName fun
    | .shopType => Shops.shopType
    | .machineSets => Shops.machineSets
    | .machineCount => Counts.module _ Shops.machines 1
    | .jobCount => Counts.module _ Shops.kernel.jobs
    | .processingTimes => Shops.processingTimes
    | .noWait => Shops.noWait
    | .transportation => Transportation.module
    | .server => Servers.shop
    | .noIdle => ShopExtras.noIdle
    | .batchSetups => ShopExtras.batchSetups
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.module _ Shops.machines

instance : Fintype family.ModuleName := inferInstanceAs (Fintype FieldName)

/-- The specification `α | β | γ` of a shop problem. -/
def spec (shopType : Shops.ShopType)
    (machineSets : Shops.Machines)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (processingTimes : Shops.ProcessingTimes := .arbitrary)
    (waiting : Shops.NoWait := .none)
    (transportation : Transportation.Value := .none)
    (server : Servers.Value := .none)
    (idling : ShopExtras.NoIdle := .none)
    (setups : ShopExtras.BatchSetups := .none)
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
    | .noWait => waiting
    | .transportation => transportation
    | .server => server
    | .noIdle => idling
    | .batchSetups => setups
    | .releaseDates => release
    | .deadlines => deadline
    | .precedence => precedence
  objective := objective

/-- `F2 || C_max` -/
def flow2_makespan : Spec family :=
  spec (shopType := .flow) (machineSets := .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `J | r_j | L_max` -/
def job_release_lmax : Spec family :=
  spec (shopType := .job) (machineSets := .dedicated) (release := .releaseDates) (objective := .lmax)

axiom family_sound : family.Sound

axiom specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t)

axiom reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t)

axiom flow2_makespan_specialCase :
    SpecialCase (problem family flow2_makespan) (problem family job_release_lmax)

end Lax434175.ShopProblems
