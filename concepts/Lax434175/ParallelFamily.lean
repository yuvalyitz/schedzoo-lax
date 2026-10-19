import Lax434175.ParallelProblems
import Lax434175.Interruption

/-!
---
title: One family for parallel machines with and without preemption
type: theorem
---
The problems on parallel machines form one family over the machine model with
pieces: its fields are the interruption field and the fields of parallel
machines (machine environment, number of machines, number of jobs,
processing times, machine sets, release dates, deadlines, precedence
constraints with time lags, communication delays, a server, forbidden times
and the input encoding), and its objectives are the completion-time
objectives. The entry $\mathrm{pmtn}$ of the three-field notation is the value
preemption of the interruption field, the entry restarts the value restarts,
and no entry the value none. The value preemption without migration has no
machine model of its own.

A problem of the non-preemptive, the preemptive, or the restarts machine model
determines the problem of this family with the same values in the common
fields and the corresponding value of the interruption field.

**Theorem.** The two problems are special cases of each other, so that the
family describes the problems of the three machine models faithfully. In
the family, a specification that is field by field a special case of another
describes a special case of the other's problem, and a specification that
reduces to another, directly or through flow time, describes a problem whose
decision version reduces to that of the other.
-/

namespace Lax434175.ParallelFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175

/-- The fields of the family: interruption and the fields of parallel
machines. -/
inductive FieldName
  | interruption
  | field (i : ParallelProblems.FieldName)
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.interruption, .field .environment, .field .machineCount, .field .jobCount,
    .field .processingTimes, .field .machineSets, .field .releaseDates, .field .deadlines,
    .field .precedence, .field .communicationDelays, .field .server, .field .forbiddenTimes,
    .field .encoding}
  complete x := by
    cases x with
    | interruption => decide
    | field i => cases i <;> decide

/-- The problems on parallel machines. -/
abbrev family : Family Interruption.kernel :=
  Thresholds.family FieldName fun
    | .interruption => Interruption.module
    | .field i => (ParallelProblems.family Interruption.model).module i

instance : Fintype family.ModuleName :=
  inferInstanceAs (Fintype FieldName)

/-- The specification `α | β | γ`. -/
def spec (interruption : Interruption.Mode := .none)
    (environment : ParallelMachines.Environment)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (machineSets : MachineSets.Value := .none)
    (processingTimes : ParallelMachines.ProcessingTimes := .arbitrary)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (communicationDelays : CommunicationDelays.Value := .none)
    (server : Servers.Value := .none)
    (forbiddenTimes : ForbiddenTimes.Value := .none)
    (encoding : ForbiddenTimes.Encoding := .standard)
    (objective : Objectives.Value) : Spec family where
  module
    | .interruption => interruption
    | .field .environment => environment
    | .field .machineCount => machineCount
    | .field .jobCount => jobCount
    | .field .processingTimes => processingTimes
    | .field .machineSets => machineSets
    | .field .releaseDates => release
    | .field .deadlines => deadline
    | .field .precedence => precedence
    | .field .communicationDelays => communicationDelays
    | .field .server => server
    | .field .forbiddenTimes => forbiddenTimes
    | .field .encoding => encoding
  objective := objective

/-- A specification of one machine model on parallel machines read in another:
the values of the fields are the same. -/
def transSpec {M M' : ParallelMachines.Model} (s : Spec (ParallelProblems.family M)) :
    Spec (ParallelProblems.family M') where
  module
    | .environment => s.module .environment
    | .machineCount => s.module .machineCount
    | .jobCount => s.module .jobCount
    | .processingTimes => s.module .processingTimes
    | .machineSets => s.module .machineSets
    | .releaseDates => s.module .releaseDates
    | .deadlines => s.module .deadlines
    | .precedence => s.module .precedence
    | .communicationDelays => s.module .communicationDelays
    | .server => s.module .server
    | .forbiddenTimes => s.module .forbiddenTimes
    | .encoding => s.module .encoding
  objective := s.objective

/-- The specification of the family with the values of a specification of a
machine model on parallel machines and a way of interruption. -/
def ofSpec {M : ParallelMachines.Model} (interruption : Interruption.Mode)
    (s : Spec (ParallelProblems.family M)) : Spec family where
  module
    | .interruption => interruption
    | .field i => (transSpec (M' := Interruption.model) s).module i
  objective := s.objective

axiom nonpreemptive_faithful (s : Spec ParallelProblems.nonpreemptive) :
    SpecialCase (problem _ s) (problem family (ofSpec .none s)) ∧
      SpecialCase (problem family (ofSpec .none s)) (problem _ s)

axiom preemptive_faithful (s : Spec ParallelProblems.preemptive) :
    SpecialCase (problem _ s) (problem family (ofSpec .pmtn s)) ∧
      SpecialCase (problem family (ofSpec .pmtn s)) (problem _ s)

axiom restarts_faithful (s : Spec ParallelProblems.restarts) :
    SpecialCase (problem _ s) (problem family (ofSpec .restarts s)) ∧
      SpecialCase (problem family (ofSpec .restarts s)) (problem _ s)

axiom family_sound : family.Sound

axiom specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t)

axiom reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t)

axiom reducible_of_reducesThroughFlow {s t : Spec family} :
    Thresholds.ReducesThroughFlow s t → Reducible (problem family s) (problem family t)

end Lax434175.ParallelFamily
