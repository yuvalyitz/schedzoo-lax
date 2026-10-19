import Lax434175.OperationsFamily
import Lax434175.BatchFamily

/-!
---
title: Maximum lateness against deadlines
type: theorem
---
The maximum lateness is at most $D$ exactly if some schedule meets the
deadlines $\bar d_j = d_j + D$; a schedule that meets them has makespan at
most the largest of them. So the decision version of a problem minimizing the
maximum lateness without deadlines reduces to that of the problem with the
deadlines $d_j + D$ that minimizes the makespan, with the largest deadline as
threshold. If some $d_j + D$ is negative, or there are no jobs and $D$ is
negative, the threshold is $-1$.

A specification $s$ of the family with operations, or of the batching family,
reduces to $t$ through deadlines if $s$ minimizes the maximum lateness without
deadlines and the specification obtained by giving it deadlines and the
makespan as objective is field by field a special case of $t$. The relation is
decidable.

**Theorem.** In both families, a specification that reduces to another through
deadlines describes a problem whose decision version reduces to that of the
other.
-/

namespace Lax434175.DeadlineSteps
open Lax434175.Problems Lax434175.Assembly
open Lax434175

/-- The value without deadlines. -/
def noDeadlines : Deadlines.Value → Bool
  | .none => true
  | _ => false

/-- The specification with deadlines and the makespan as objective. -/
def opsWithDeadlines (s : Spec OperationsFamily.family) : Spec OperationsFamily.family where
  module
    | .deadlines => Deadlines.Value.deadlines
    | i => s.module i
  objective := .makespan

/-- `s` minimizes the maximum lateness without deadlines, and with deadlines and
the makespan it is field by field a special case of `t`. -/
def OpsReducesThroughDeadlines (s t : Spec OperationsFamily.family) : Prop :=
  Thresholds.objectiveOf s = .lmax ∧ noDeadlines (s.module .deadlines) = true ∧ (opsWithDeadlines s).le t

instance (s t : Spec OperationsFamily.family) : Decidable (OpsReducesThroughDeadlines s t) := by
  unfold OpsReducesThroughDeadlines
  infer_instance

/-- The batching specification with deadlines and the makespan as objective. -/
def batchWithDeadlines (s : Spec BatchFamily.family) : Spec BatchFamily.family where
  module
    | .field .deadlines => Deadlines.Value.deadlines
    | i => s.module i
  objective := .makespan

def BatchReducesThroughDeadlines (s t : Spec BatchFamily.family) : Prop :=
  Thresholds.objectiveOf s = .lmax ∧ noDeadlines (s.module (.field .deadlines)) = true ∧
    (batchWithDeadlines s).le t

instance (s t : Spec BatchFamily.family) : Decidable (BatchReducesThroughDeadlines s t) := by
  unfold BatchReducesThroughDeadlines
  infer_instance

axiom ops_reducible {s t : Spec OperationsFamily.family} :
    OpsReducesThroughDeadlines s t →
      Reducible (problem OperationsFamily.family s) (problem OperationsFamily.family t)

axiom batch_reducible {s t : Spec BatchFamily.family} :
    BatchReducesThroughDeadlines s t →
      Reducible (problem BatchFamily.family s) (problem BatchFamily.family t)

end Lax434175.DeadlineSteps
