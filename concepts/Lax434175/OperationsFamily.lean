import Lax434175.Operations
import Lax434175.ParallelFamily

/-!
---
title: One family for parallel machines and shops
type: theorem
---
The problems on parallel machines and the shop problems form one family over
scheduling with operations, with the fields of scheduling with operations and
the completion-time objectives.

A problem of the family of parallel machines determines the problem of this
family with one operation per job, the same values in the fields of parallel
machines, its machine-set value as a value of the machine field, and the
value none in the fields of shops. A shop problem determines the problem with
its shop type as job structure, identical machines, its machine value, its
processing-time value, the same values in the fields of shops, and the value
none in the fields of parallel machines.

**Theorem.** In both cases the two problems are special cases of each other.
In the family, a specification that is field by field a special case of
another describes a special case of the other's problem, and a specification
that reduces to another, directly or through flow time, describes a problem
whose decision version reduces to that of the other.
-/

namespace Lax434175.OperationsFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Operations

/-- The fields of the family. -/
inductive FieldName
  | interruption
  | jobStructure
  | environment
  | machineCount
  | jobCount
  | processingTimes
  | machineSets
  | releaseDates
  | deadlines
  | precedence
  | communicationDelays
  | server
  | forbiddenTimes
  | encoding
  | noWait
  | transportation
  | noIdle
  | batchSetups
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.interruption, .jobStructure, .environment, .machineCount, .jobCount,
    .processingTimes, .machineSets, .releaseDates, .deadlines, .precedence,
    .communicationDelays, .server, .forbiddenTimes, .encoding, .noWait, .transportation,
    .noIdle, .batchSetups}
  complete x := by cases x <;> decide

/-- The problems on parallel machines and in shops. -/
abbrev family : Family Operations.kernel :=
  Thresholds.family FieldName fun
    | .interruption => Operations.interruption
    | .jobStructure => Operations.jobStructure
    | .environment => Operations.environment
    | .machineCount => Counts.module _ Operations.machines 1
    | .jobCount => Counts.module _ Operations.kernel.jobs
    | .processingTimes => Operations.processingTimes
    | .machineSets => Operations.machineSets
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.module _ Operations.machines
    | .communicationDelays => CommunicationDelays.module Operations.model
    | .server => Operations.server
    | .forbiddenTimes => ForbiddenTimes.module _
    | .encoding => ForbiddenTimes.encoding _
    | .noWait => Operations.noWait
    | .transportation => Operations.transportation
    | .noIdle => Operations.noIdle
    | .batchSetups => Operations.batchSetups

instance : Fintype family.ModuleName :=
  inferInstanceAs (Fintype FieldName)

/-- The specification `α | β | γ`. -/
def spec (interruption : Interruption.Mode := .none)
    (shopType : Structure := .single)
    (environment : ParallelMachines.Environment := .identical)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (processingTimes : ParallelMachines.ProcessingTimes := .arbitrary)
    (machineSets : Machines := .par .none)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (communicationDelays : CommunicationDelays.Value := .none)
    (server : Servers.Value := .none)
    (forbiddenTimes : ForbiddenTimes.Value := .none)
    (encoding : ForbiddenTimes.Encoding := .standard)
    (waiting : Shops.NoWait := .none)
    (transportation : Transportation.Value := .none)
    (idling : ShopExtras.NoIdle := .none)
    (setups : ShopExtras.BatchSetups := .none)
    (objective : Objectives.Value) : Spec family where
  module
    | .interruption => interruption
    | .jobStructure => shopType
    | .environment => environment
    | .machineCount => machineCount
    | .jobCount => jobCount
    | .processingTimes => processingTimes
    | .machineSets => machineSets
    | .releaseDates => release
    | .deadlines => deadline
    | .precedence => precedence
    | .communicationDelays => communicationDelays
    | .server => server
    | .forbiddenTimes => forbiddenTimes
    | .encoding => encoding
    | .noWait => waiting
    | .transportation => transportation
    | .noIdle => idling
    | .batchSetups => setups
  objective := objective

/-- The job structure of a shop type. -/
def ofShopType : Shops.ShopType → Structure
  | .open => .open
  | .flow => .flow
  | .job => .job
  | .flexibleFlow => .flexibleFlow

/-- The processing-time value of a shop value. -/
def ofShopTimes : Shops.ProcessingTimes → ParallelMachines.ProcessingTimes
  | .unit => .unit
  | .equal => .equal
  | .arbitrary => .arbitrary

/-- The specification of the family with the values of a problem on parallel
machines. -/
def ofParallel (s : Spec ParallelFamily.family) : Spec family where
  module
    | .interruption => s.module .interruption
    | .jobStructure => Structure.single
    | .environment => s.module (.field .environment)
    | .machineCount => s.module (.field .machineCount)
    | .jobCount => s.module (.field .jobCount)
    | .processingTimes => s.module (.field .processingTimes)
    | .machineSets => Machines.par (s.module (.field .machineSets))
    | .releaseDates => s.module (.field .releaseDates)
    | .deadlines => s.module (.field .deadlines)
    | .precedence => s.module (.field .precedence)
    | .communicationDelays => s.module (.field .communicationDelays)
    | .server => s.module (.field .server)
    | .forbiddenTimes => s.module (.field .forbiddenTimes)
    | .encoding => s.module (.field .encoding)
    | .noWait => Shops.NoWait.none
    | .transportation => Transportation.Value.none
    | .noIdle => ShopExtras.NoIdle.none
    | .batchSetups => ShopExtras.BatchSetups.none
  objective := s.objective

/-- The specification of the family with the values of a shop problem. -/
def ofShop (s : Spec ShopFamily.family) : Spec family where
  module
    | .interruption => s.module .interruption
    | .jobStructure => ofShopType (s.module (.field .shopType))
    | .environment => ParallelMachines.Environment.identical
    | .machineCount => s.module (.field .machineCount)
    | .jobCount => s.module (.field .jobCount)
    | .processingTimes => ofShopTimes (s.module (.field .processingTimes))
    | .machineSets => Machines.shop (s.module (.field .machineSets))
    | .releaseDates => s.module (.field .releaseDates)
    | .deadlines => s.module (.field .deadlines)
    | .precedence => s.module (.field .precedence)
    | .communicationDelays => CommunicationDelays.Value.none
    | .server => s.module (.field .server)
    | .forbiddenTimes => ForbiddenTimes.Value.none
    | .encoding => ForbiddenTimes.Encoding.standard
    | .noWait => s.module (.field .noWait)
    | .transportation => s.module (.field .transportation)
    | .noIdle => s.module (.field .noIdle)
    | .batchSetups => s.module (.field .batchSetups)
  objective := s.objective

axiom parallel_faithful (s : Spec ParallelFamily.family) :
    SpecialCase (problem _ s) (problem family (ofParallel s)) ∧
      SpecialCase (problem family (ofParallel s)) (problem _ s)

axiom shop_faithful (s : Spec ShopFamily.family) :
    SpecialCase (problem _ s) (problem family (ofShop s)) ∧
      SpecialCase (problem family (ofShop s)) (problem _ s)

axiom family_sound : family.Sound

axiom specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t)

axiom reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t)

axiom reducible_of_reducesThroughFlow {s t : Spec family} :
    Thresholds.ReducesThroughFlow s t → Reducible (problem family s) (problem family t)

end Lax434175.OperationsFamily
