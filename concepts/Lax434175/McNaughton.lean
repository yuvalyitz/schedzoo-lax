import Lax434175.ZooParallel
import Lax434175.ZooPreemptive
import Lax434175.Parameters

/-!
---
title: Preemption does not help the total weighted completion time
type: theorem
---
McNaughton (1959), Theorem 4.1: on identical parallel machines, every
preemptive schedule can be turned into one without preemption whose total
weighted completion time is not larger. The proof is an exchange: in a
schedule with $b$ split times, the jobs around the last one are rearranged in
one of two ways, whose changes of the cost are $c(X - Y)$ and $-e(X - Y)$ for
sums of weights $X$ and $Y$; one of them is not positive, and it leaves $b - 1$
split times.

Without preemption a schedule is also a preemptive one, so
$P \mid\mid \sum w_jC_j$ is a special case of $P \mid pmtn \mid \sum w_jC_j$ field
by field. The theorem gives the converse, for every bound on the number of
machines: the same kernel instance, the same data and parameters in every field
except interruption (which changes from preemption to none and carries no data),
and the same threshold. The interruption field cannot be kept: a reduction in
place in the sense of `Parameters.InPlace` would keep every invariant field
parameter, and whether an instance is read with preemption is one.

**Theorem.** For every bound on the number of machines, the decision version of
$P \mid pmtn \mid \sum w_jC_j$ reduces to that of $P \mid\mid \sum w_jC_j$ with the
same kernel instance, the same parameters of every field other than
interruption, and the same threshold; in particular the zoo's
$P \mid pmtn \mid \sum w_jC_j$ and $P2 \mid pmtn \mid \sum w_jC_j$ reduce to
$P \mid\mid \sum w_jC_j$ and $P2 \mid\mid \sum w_jC_j$.
-/

namespace Lax434175.McNaughton
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Parameters

/-- `P|pmtn|ΣwjCj` with a bound on the number of machines. -/
def preemptive (b : Counts.Bound) : Spec OperationsFamily.family :=
  OperationsFamily.spec (interruption := .pmtn) (machineCount := b) (objective := .sumWC)

/-- `P||ΣwjCj` with the same bound. -/
def nonpreemptive (b : Counts.Bound) : Spec OperationsFamily.family :=
  OperationsFamily.spec (machineCount := b) (objective := .sumWC)

/-- **McNaughton's theorem.** The same instance, every field but interruption
kept, and the same threshold. -/
axiom preemption_useless (b : Counts.Bound) :
    ∃ r : DecisionReduction (problem OperationsFamily.family (preemptive b))
        (problem OperationsFamily.family (nonpreemptive b)),
      r.Sound ∧ (∀ x D, (r.map x D).base = x.base) ∧
      (∀ i, i ≠ OperationsFamily.FieldName.interruption →
        ∀ (κ : FieldParameter (OperationsFamily.family.module i)) x D,
          ofField OperationsFamily.family i κ (nonpreemptive b) (r.map x D) =
            ofField OperationsFamily.family i κ (preemptive b) x) ∧
      ∀ x D, r.threshold x D = D

/-- The zoo's `P|pmtn|ΣwjCj` reduces to `P||ΣwjCj`. -/
axiom zoo_any :
    Reducible (problem OperationsFamily.family ZooPreemptive.p39)
      (problem OperationsFamily.family ZooParallel.p2)

/-- The zoo's `P2|pmtn|ΣwjCj` reduces to `P2||ΣwjCj`. -/
axiom zoo_two :
    Reducible (problem OperationsFamily.family ZooPreemptive.p11)
      (problem OperationsFamily.family ZooParallel.p32)

end Lax434175.McNaughton
