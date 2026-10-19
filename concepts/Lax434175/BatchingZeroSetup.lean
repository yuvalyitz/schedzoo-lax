import Lax434175.PreemptionUseless

/-!
---
title: Scheduling on one machine as batching
type: theorem
---
Batching with setup time $0$ and batches of at most one job is scheduling on a
single machine: the batches are processed one after the other, and a batch
with one job takes the processing time of that job, in serial and in parallel
batching alike. Conversely, numbering the jobs of a non-preemptive schedule on
one machine by start time (ties by completion time and then by number) and
putting each job in a batch of its own gives such a batch schedule with the
same start and completion times.

In serial batching the capacity may also be unbounded. With setup time $0$,
splitting a batch into its jobs, processed one after the other in the order of
their numbers from the start of the batch, completes no job later and starts
none earlier than the batch. For a regular objective, one that does not
decrease when a completion time grows (every objective here except the
just-in-time ones), a batch schedule therefore gives a schedule on one
machine of no larger cost.

Hence a problem of the family with operations that has one operation per job,
one machine, no interruption, no machine-set restriction, processing times
unit, equal or arbitrary, a precedence class other than $A_m$-orders, and
none of the server, forbidden times, no-idle constraints and batch setups,
reduces to the batching problem with the same number of jobs, processing
times, release dates, deadlines, precedence constraints and objective: with
bounded capacity, in either mode, and with unbounded capacity in serial mode
when the objective is regular.

A specification $s$ of the family with operations reduces to a specification
$t$ of the batching family if $s$ is of this kind and the batching
specification obtained from it, in a mode and a capacity allowed for it, is
field by field a special case of $t$.

**Theorem.** A specification that reduces to a batching specification
describes a problem whose decision version reduces to that of the batching
problem.
-/

namespace Lax434175.BatchingZeroSetup
open Lax434175.Problems Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily Lax434175.TimeReversal
open Lax434175.PreemptionUseless

def isNoneMode : Interruption.Mode → Bool
  | .none => true
  | _ => false

def noSets : Machines → Bool
  | .par .none => true
  | _ => false

def notAOrder : Precedence.Order → Bool
  | .aOrder => false
  | _ => true

/-- The processing-time value of batching with the same instances. -/
def batchTimes : ParallelMachines.ProcessingTimes → Option Batching.ProcessingTimes
  | .unit => some .unit
  | .equal => some .equal
  | .arbitrary => some .arbitrary
  | .oneOrTwo => none

/-- The specification is a single-machine problem that batching expresses. -/
def Applies (s : Spec family) : Bool :=
  isNoneMode (s.module .interruption) && isSingle (s.module .jobStructure) &&
    atMostOne (s.module .machineCount) && (batchTimes (s.module .processingTimes)).isSome &&
    noSets (s.module .machineSets) && notAOrder (s.module .precedence).order &&
    noServer (s.module .server) && noForbidden (s.module .forbiddenTimes) &&
    noIdling (s.module .noIdle) && noSetups (s.module .batchSetups)

/-- The objective does not decrease when a completion time grows: every
objective except the just-in-time ones. -/
def isRegular (o : Objectives.Value) : Bool :=
  Objectives.kind o != .notJustInTime

/-- The capacities a single-machine problem is read in: at most one job per
batch in either mode, and unbounded capacity in serial mode for a regular
objective. -/
def capacityAllowed : Batching.Mode → Batching.Capacity → Objectives.Value → Bool
  | _, .bounded, _ => true
  | .serial, .unbounded, o => isRegular o
  | _, _, _ => false

/-- The batching specification of a single-machine specification. -/
def toBatch (s : Spec family) (mode : Batching.Mode) (times : Batching.ProcessingTimes)
    (capacity : Batching.Capacity) : Spec BatchFamily.family where
  module
    | .mode => mode
    | .field .capacity => capacity
    | .field .jobCount => s.module .jobCount
    | .field .processingTimes => times
    | .field .releaseDates => s.module .releaseDates
    | .field .deadlines => s.module .deadlines
    | .field .precedence => s.module .precedence
  objective := s.objective

/-- `s` reduces to the batching specification `t`. -/
def ReducesToBatching (s : Spec family) (t : Spec BatchFamily.family) : Prop :=
  Applies s = true ∧ ∃ mode times capacity, batchTimes (s.module .processingTimes) = some times ∧
    capacityAllowed mode capacity s.objective = true ∧ (toBatch s mode times capacity).le t

instance (s : Spec family) (t : Spec BatchFamily.family) : Decidable (ReducesToBatching s t) := by
  unfold ReducesToBatching
  cases h : batchTimes (s.module .processingTimes) with
  | none => exact isFalse fun ⟨_, _, _, _, hm, _⟩ => by simp at hm
  | some w =>
    exact decidable_of_iff (Applies s = true ∧
      ∃ mode ∈ [Batching.Mode.serial, .parallel],
        ∃ capacity ∈ [Batching.Capacity.unbounded, .bounded, .sizes],
          capacityAllowed mode capacity s.objective = true ∧ (toBatch s mode w capacity).le t)
      ⟨fun ⟨h1, mode, _, capacity, _, h2, h3⟩ => ⟨h1, mode, w, capacity, rfl, h2, h3⟩,
       fun ⟨h1, mode, w', capacity, hw, h2, h3⟩ => by
        cases hw
        refine ⟨h1, mode, ?_, capacity, ?_, h2, h3⟩
        · cases mode <;> simp
        · cases capacity <;> simp⟩

axiom reducible_of_reducesToBatching {s : Spec family} {t : Spec BatchFamily.family} :
    ReducesToBatching s t → Reducible (problem family s) (problem BatchFamily.family t)

end Lax434175.BatchingZeroSetup
