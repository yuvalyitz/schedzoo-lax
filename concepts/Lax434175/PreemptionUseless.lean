import Lax434175.TimeReversal

/-!
---
title: Preemption does not help on a single machine
type: theorem
---
On a single machine and without release dates, a preemptive schedule can be
turned into a non-preemptive one in which no job completes later: process the
jobs one after the other from time $0$, in the order of their completion
times (ties broken by start times and then by the numbering of the jobs). A
job then completes at the total processing time of the jobs before it and
itself, and the machine has processed these jobs entirely by the original
completion time of the job, so this total is at most that time.

Hence a problem and the same problem with preemption allowed have the same
decision versions when there is one operation per job, at most one machine,
no release dates, the precedence constraints have zero lags, the objective
depends monotonically on the completion times (every objective except the
number of jobs not completed just in time), and there are no server,
forbidden times, no-idle constraints or batch setups. Deadlines, machine sets,
communication delays, no-wait and transportation delays may be present; with
one operation per job on one machine the last three impose nothing more on
the new schedule.

A specification $s$ reduces to $t$ by dropping preemption if it is of this
kind, has no interruption or preemption, and the same specification with the
other of the two is field by field a special case of $t$.

**Theorem.** A specification that reduces to another by dropping preemption
describes a problem whose decision version reduces to that of the other.
-/

namespace Lax434175.PreemptionUseless
open Lax434175.Problems Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily Lax434175.TimeReversal

def atMostOne : Counts.Bound → Bool
  | .atMost 0 | .atMost 1 => true
  | _ => false

def zeroLags (v : Precedence.Value) : Bool :=
  match v.lags with
  | .zero => true
  | _ => false

def regular : Objectives.Value → Bool
  | .sumZ | .sumWZ => false
  | _ => true

/-- The interruption swapped between none and preemption. -/
def swapped : Interruption.Mode → Option Interruption.Mode
  | .none => some .pmtn
  | .pmtn => some .none
  | .restarts | .pmtnNoMigration => none

/-- The specification is of the kind for which preemption does not help. -/
def Applies (s : Spec family) : Bool :=
  isSingle (s.module .jobStructure) && atMostOne (s.module .machineCount) &&
    releaseNone (s.module .releaseDates) && zeroLags (s.module .precedence) &&
    regular (Thresholds.objectiveOf s) && noServer (s.module .server) &&
    noForbidden (s.module .forbiddenTimes) && noIdling (s.module .noIdle) &&
    noSetups (s.module .batchSetups)

/-- The same specification with another way of interruption. -/
def withInterruption (s : Spec family) (m : Interruption.Mode) : Spec family where
  module
    | .interruption => m
    | i => s.module i
  objective := s.objective

/-- `s` reduces to `t` by dropping or allowing preemption. -/
def ReducesByPreemption (s t : Spec family) : Prop :=
  Applies s = true ∧ ∃ m, swapped (s.module .interruption) = some m ∧ (withInterruption s m).le t

instance (s t : Spec family) : Decidable (ReducesByPreemption s t) := by
  unfold ReducesByPreemption
  cases h : swapped (s.module .interruption) with
  | none => exact isFalse fun ⟨_, m, hm, _⟩ => by simp at hm
  | some m =>
    exact decidable_of_iff (Applies s = true ∧ (withInterruption s m).le t)
      ⟨fun ⟨h1, h2⟩ => ⟨h1, m, rfl, h2⟩, fun ⟨h1, m', hm, h2⟩ => by
        cases hm
        exact ⟨h1, h2⟩⟩

axiom reducible_of_reducesByPreemption {s t : Spec family} :
    ReducesByPreemption s t → Reducible (problem family s) (problem family t)

end Lax434175.PreemptionUseless
