import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Lax434175.Problems

/-!
---
title: Single-machine scheduling with rejection
type: definition
---
The problem $1 \mid \sum_{j \in \mathrm{reject}} e_j \le B \mid \sum C_j$. An
instance has $n$ jobs with processing times $p_j$ and rejection costs $e_j$,
and a budget $B$. A solution rejects some jobs and assigns a start time to
every accepted job. It is feasible if the rejection costs of the rejected
jobs sum to at most $B$ and no two accepted jobs overlap on the machine. The
cost is the total completion time of the accepted jobs.
-/

namespace Lax434175.Rejection
open Lax434175.Problems

structure Inst where
  jobs : ℕ
  p : Fin jobs → ℕ
  /-- The rejection cost of a job. -/
  e : Fin jobs → ℕ
  budget : ℕ

structure Sched (x : Inst) where
  /-- The accepted jobs. -/
  accepted : Finset (Fin x.jobs)
  start : Fin x.jobs → ℕ

def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ := σ.start j + x.p j

/-- The rejected jobs respect the budget and the accepted jobs do not
overlap. -/
def feasible (x : Inst) (σ : Sched x) : Prop :=
  ∑ j ∈ Finset.univ \ σ.accepted, x.e j ≤ x.budget ∧
  ∀ i ∈ σ.accepted, ∀ j ∈ σ.accepted, i ≠ j →
    completion x σ i ≤ σ.start j ∨ completion x σ j ≤ σ.start i

/-- `1 | Σ_{j ∈ reject} e_j ≤ B | ΣC_j` -/
def problem : Problem where
  Inst := Inst
  Sched := Sched
  feasible := feasible
  cost x σ := ((∑ j ∈ σ.accepted, completion x σ j : ℕ) : ℚ)

end Lax434175.Rejection
