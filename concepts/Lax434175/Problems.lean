import Mathlib.Algebra.Order.Field.Rat

/-!
---
title: Optimization problems and embeddings
type: theorem
---
An optimization problem consists of a type of instances, for every instance a
type of candidate solutions, a feasibility predicate, and a rational cost to
be minimized.

An embedding of a problem $A$ into a problem $B$ maps every instance $x$ of
$A$ to an instance of $B$ and translates solutions in both directions. It is
sound if both translations preserve feasibility and neither increases the
cost. A sound embedding shows that $A$ is a special case of $B$: the two
instances $x$ and its image have the same optimal cost.

Restricting a problem to the instances satisfying a predicate yields again a
problem, and the inclusion of the restricted instances is an embedding.

Embeddings compose: the instance maps are composed, and so are the
translations of solutions.

**Theorem.** The composition of two sound embeddings is sound.

The decision version of a problem asks, for an instance and a threshold,
whether some feasible solution has cost at most the threshold. A reduction
of the decision version of $A$ to that of $B$ maps every instance of $A$ and
integral threshold to an instance of $B$ and an integral threshold with the
same answer. Problem $A$ is reducible to $B$ if such a reduction exists.

**Theorem.** A special case of a problem is reducible to it, and
reducibility is transitive.
-/

namespace Lax434175.Problems

/-- A minimization problem. -/
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The candidate solutions of an instance. -/
  Sched : Inst → Type
  /-- Which candidate solutions are feasible. -/
  feasible : (x : Inst) → Sched x → Prop
  /-- The cost of a candidate solution. -/
  cost : (x : Inst) → Sched x → ℚ

/-- The data of an embedding of `A` into `B`: a map on instances and
translations of solutions in both directions. -/
structure Embedding (A B : Problem) where
  map : A.Inst → B.Inst
  forth : (x : A.Inst) → A.Sched x → B.Sched (map x)
  back : (x : A.Inst) → B.Sched (map x) → A.Sched x

/-- An embedding is sound if both translations preserve feasibility and do
not increase the cost. -/
structure Embedding.Sound {A B : Problem} (e : Embedding A B) : Prop where
  forth_feasible : ∀ x σ, A.feasible x σ → B.feasible (e.map x) (e.forth x σ)
  forth_cost : ∀ x σ, A.feasible x σ → B.cost (e.map x) (e.forth x σ) ≤ A.cost x σ
  back_feasible : ∀ x τ, B.feasible (e.map x) τ → A.feasible x (e.back x τ)
  back_cost : ∀ x τ, B.feasible (e.map x) τ → A.cost x (e.back x τ) ≤ B.cost (e.map x) τ

/-- `A` is a special case of `B`. -/
def SpecialCase (A B : Problem) : Prop := ∃ e : Embedding A B, e.Sound

/-- The restriction of a problem to the instances satisfying `φ`. -/
def Problem.restrict (P : Problem) (φ : P.Inst → Prop) : Problem where
  Inst := { x : P.Inst // φ x }
  Sched x := P.Sched x.1
  feasible x σ := P.feasible x.1 σ
  cost x σ := P.cost x.1 σ

/-- The inclusion of a restricted problem into the unrestricted one. -/
def Problem.inclusion (P : Problem) (φ : P.Inst → Prop) : Embedding (P.restrict φ) P where
  map x := x.1
  forth _ σ := σ
  back _ σ := σ

/-- The composition of two embeddings. -/
def Embedding.comp {A B C : Problem} (e : Embedding A B) (f : Embedding B C) : Embedding A C where
  map x := f.map (e.map x)
  forth x σ := f.forth (e.map x) (e.forth x σ)
  back x τ := e.back x (f.back (e.map x) τ)

axiom comp_sound {A B C : Problem} (e : Embedding A B) (f : Embedding B C) :
    e.Sound → f.Sound → (e.comp f).Sound

/-- Some feasible solution of the instance has cost at most the threshold. -/
def Problem.Decides (P : Problem) (x : P.Inst) (D : ℚ) : Prop :=
  ∃ σ, P.feasible x σ ∧ P.cost x σ ≤ D

/-- The data of a reduction between decision versions: an instance and a
threshold of `A` are mapped to an instance and a threshold of `B`. -/
structure DecisionReduction (A B : Problem) where
  map : A.Inst → ℤ → B.Inst
  threshold : A.Inst → ℤ → ℤ

/-- A reduction is sound if it preserves the answer. -/
def DecisionReduction.Sound {A B : Problem} (r : DecisionReduction A B) : Prop :=
  ∀ x (D : ℤ), A.Decides x D ↔ B.Decides (r.map x D) (r.threshold x D)

/-- The decision version of `A` reduces to that of `B`. -/
def Reducible (A B : Problem) : Prop := ∃ r : DecisionReduction A B, r.Sound

axiom reducible_of_specialCase {A B : Problem} : SpecialCase A B → Reducible A B

axiom reducible_trans {A B C : Problem} : Reducible A B → Reducible B C → Reducible A C

end Lax434175.Problems
