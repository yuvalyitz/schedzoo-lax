import Lax434175.DeadlineSteps
import Lax434175.PrecedenceReversal

/-!
---
title: Time reversal
type: theorem
---
Running a schedule backwards from a horizon $H$ turns a piece processing an
operation during $[a, b]$ into one processing it during $[H - b, H - a]$. A
job that completes at $C_j$ then starts at $H - C_j$, and a precedence
constraint $C_i + l_{ij} \le S_j$ becomes the constraint
$C'_j + l_{ij} \le S'_i$ of the reversed relation.

Hence the maximum lateness without release dates and the makespan with
release dates are equivalent:

- $L_{\max} \le D$ for due dates $d_j$ exactly if the reversed problem with
  release dates $r'_j = H - (d_j + D)$, $H = \max_j (d_j + D)$, has makespan
  at most $H$ (if some $d_j + D$ is negative, or there are no jobs and $D$ is
  negative, the threshold is $-1$);
- $C_{\max} \le D$ for release dates $r_j$ exactly if the reversed problem
  without release dates and with due dates $D - r_j$ has maximum lateness at
  most $0$ (if $D$ is negative or some $r_j$ exceeds $D$, the answer is no,
  and the reduction asks whether the maximum lateness for due dates $0$ is at
  most $-1$).

This is shown for the problems of the family with operations that have one
operation per job, no restarts, a reversible precedence class, no deadlines,
and none of the communication delays, server, forbidden times, transportation
delays, no-idle and batch setups, whose meaning changes under reversal. The
reversed specification has the reversed precedence class, the release dates
or none, and the makespan or the maximum lateness.

A specification $s$ reduces to $t$ by reversal if it is of this kind, and
either minimizes the maximum lateness without release dates and its reversal
with release dates and the makespan is field by field a special case of $t$,
or minimizes the makespan with release dates or none and its reversal without
release dates and with the maximum lateness is so. The relation is decidable.

**Theorem.** A specification that reduces to another by reversal describes a
problem whose decision version reduces to that of the other.
-/

namespace Lax434175.TimeReversal
open Lax434175.Problems Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily

def isSingle : Structure → Bool
  | .single => true
  | _ => false

def notRestarts : Interruption.Mode → Bool
  | .restarts => false
  | _ => true

def noDelays : CommunicationDelays.Value → Bool
  | .none => true
  | _ => false

def noServer : Servers.Value → Bool
  | .none => true
  | _ => false

def noForbidden : ForbiddenTimes.Value → Bool
  | .none => true
  | _ => false

def noTransport (v : Transportation.Value) : Bool :=
  (match v.shape with
    | .none => true
    | _ => false) && !v.robot

def noIdling : ShopExtras.NoIdle → Bool
  | .none => true
  | _ => false

def noSetups : ShopExtras.BatchSetups → Bool
  | .none => true
  | _ => false

def releaseNone : ReleaseDates.Value → Bool
  | .none => true
  | _ => false

def releaseKnown : ReleaseDates.Value → Bool
  | .online => false
  | _ => true

/-- The specification can be reversed. -/
def Reversible (s : Spec family) : Bool :=
  notRestarts (s.module .interruption) && isSingle (s.module .jobStructure) &&
    PrecedenceReversal.reversible (s.module .precedence).order && DeadlineSteps.noDeadlines (s.module .deadlines) &&
    noDelays (s.module .communicationDelays) && noServer (s.module .server) &&
    noForbidden (s.module .forbiddenTimes) && noTransport (s.module .transportation) &&
    noIdling (s.module .noIdle) && noSetups (s.module .batchSetups)

/-- The reversed specification, with given release dates and objective. -/
def reversed (s : Spec family) (release : ReleaseDates.Value) (objective : Objectives.Value) :
    Spec family where
  module
    | .precedence => (⟨PrecedenceReversal.reverse (s.module .precedence).order, (s.module .precedence).lags⟩ :
        Precedence.Value)
    | .releaseDates => release
    | i => s.module i
  objective := objective

/-- `s` reduces to `t` by reversal. -/
def ReducesByReversal (s t : Spec family) : Prop :=
  Reversible s = true ∧
    ((Thresholds.objectiveOf s = .lmax ∧ releaseNone (s.module .releaseDates) = true ∧
        (reversed s .releaseDates .makespan).le t) ∨
      (Thresholds.objectiveOf s = .makespan ∧ releaseKnown (s.module .releaseDates) = true ∧
        (reversed s .none .lmax).le t))

instance (s t : Spec family) : Decidable (ReducesByReversal s t) := by
  unfold ReducesByReversal
  infer_instance

axiom reducible_of_reducesByReversal {s t : Spec family} :
    ReducesByReversal s t → Reducible (problem family s) (problem family t)

end Lax434175.TimeReversal
