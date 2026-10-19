import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.NNRat.Defs
import Lax434175.Modules

/-!
---
title: Precedence constraints and time lags
type: theorem
---
With precedence constraints an instance carries a relation on the jobs,
given by its arcs, and a time lag $l_{ij}$ for every pair of jobs. Whenever
$i$ precedes $j$, job $j$ may not start before the completion of job $i$
plus the lag: $C_i + l_{ij} \le S_j$. A lag may be negative.

A value of the field consists of a class of relations and a kind of lags.

The classes are, with $\prec$ the transitive closure of the arcs:

- none: no relation, read as the empty relation;
- chains: every job has at most one successor and at most one predecessor;
- intree: every job has at most one successor;
- outtree: every job has at most one predecessor;
- tree: the relation is an intree or an outtree;
- opposing forest: the jobs split into two parts without arcs between them,
  one an intree and the other an outtree;
- series-parallel: $\prec$ contains no four jobs $a, b, c, d$ whose only
  relations are $a \prec c$, $b \prec c$, $b \prec d$;
- divide-and-conquer graph: a single job is one; and for two further jobs
  $s$ and $t$ and at least one divide-and-conquer graph on disjoint sets of
  jobs, so is their union with $s$, $t$ and all arcs from $s$ to the jobs of
  the graphs and from these to $t$;
- interval order: $a \prec b$ and $c \prec d$ imply $a \prec d$ or
  $c \prec b$;
- over-interval order: no five different jobs $1, \dots, 5$ are related
  exactly by $1 \prec 2$, $3 \prec 4$, $3 \prec 5$, and none exactly by the
  reverse relations $2 \prec 1$, $4 \prec 3$, $5 \prec 3$ (the structures of type
  I and II of Chardon and Moukrim, 2005);
- quasi-interval order: an over-interval order in which, moreover, no five
  different jobs are related exactly by $1 \prec 2$, $1 \prec 4$,
  $3 \prec 5 \prec 4$ and hence $3 \prec 4$ (Moukrim 1999, Definition 2: the
  structures of type I, in either orientation, and of type II);
- $A_m$-order, for the number $m$ of machines of the instance: for any two
  sets $A$ and $B$ of at most $m$ pairwise unrelated jobs, at most $m$ jobs
  of $A \cup B$ have a predecessor in $A \cup B$, and at most $m$ have a
  successor in $A \cup B$ (the property $Q_m$ of Moukrim and Quilliot, 1997);
- level order: every job of level $l + 1$ precedes every job of level $l$,
  where the level of a job is the length of the longest path of arcs
  starting from it;
- bounded height: an arbitrary relation; the value records that the length
  of its longest path is regarded as a constant;
- dimension two: the jobs can be placed in the plane such that, for
  different jobs, $i \prec j$ exactly if both coordinates of $i$ are at most
  those of $j$;
- bounded dimension: the same in a space of some dimension;
- prec: an arbitrary relation.

The class none is a special case of every class except
divide-and-conquer graphs, which have a single first and a single last job; interval orders of quasi-interval orders,
of over-interval orders and of $A_m$-orders; quasi-interval orders of over-interval orders; chains of intree
and outtree; these of tree; tree of opposing forest; dimension two of
bounded dimension; chains, the trees and opposing forests of series-parallel
orders, since every job of an intree has its successors on a chain and every job
of an outtree its predecessors; series-parallel orders of dimension two and of bounded
dimension, by the classical theorem that an order without such four jobs has
dimension at most two; and every class of prec.

The kinds of lags are: zero; unit, $l_{ij} = 1$; constant, $l_{ij} = l$, also
restricted to $l \le 0$ or to $l > 0$; and arbitrary, also restricted to
$l_{ij} \le 0$ or to $l_{ij} > 0$. A kind is a special case of another if
its lags are among the other's.

On a single machine, as in batching, every order is an $A_1$-order, so the
value says nothing there. The field of one machine leaves it out: the value
$A_m$ admits no instance and is a special case of no other value.

**Theorem.** Over every kernel, the field of precedence constraints with
time lags is sound, and so is the field of one machine.
-/

namespace Lax434175.Precedence
open Lax434175.Kernels Lax434175.Modules

inductive Order
  | none
  | chains
  | intree
  | outtree
  | tree
  | opposingForest
  | seriesParallel
  | divideAndConquer
  | intervalOrder
  | quasiInterval
  | overInterval
  | aOrder
  | levelOrder
  | boundedHeight
  | dimensionTwo
  | boundedDimension
  | prec
  deriving DecidableEq

/-- No data without precedence constraints; a relation on the jobs with them. -/
def Order.Data (n : ℕ) : Order → Type
  | .none => Unit
  | _ => Fin n → Fin n → Prop

/-- The precedence relation; empty when the class is none. -/
def Order.view {n : ℕ} : (v : Order) → v.Data n → Fin n → Fin n → Prop
  | .none, _ => fun _ _ => False
  | .chains, r | .intree, r | .outtree, r | .tree, r | .opposingForest, r
  | .seriesParallel, r | .divideAndConquer, r | .intervalOrder, r | .levelOrder, r | .boundedHeight, r
  | .quasiInterval, r | .overInterval, r | .aOrder, r
  | .dimensionTwo, r
  | .boundedDimension, r | .prec, r => r

/-- Every job has at most one successor. -/
def AtMostOneSuccessor {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ i j k, r i j → r i k → j = k

/-- Every job has at most one predecessor. -/
def AtMostOnePredecessor {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ i j k, r j i → r k i → j = k

/-- The jobs split into an intree part and an outtree part without arcs
between them. -/
def OpposingForest {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∃ inPart : Fin n → Prop, (∀ i j, r i j → (inPart i ↔ inPart j)) ∧
    (∀ i j k, inPart i → r i j → r i k → j = k) ∧
    (∀ i j k, ¬ inPart i → r j i → r k i → j = k)

/-- No four jobs are related exactly by `a ≺ c`, `b ≺ c`, `b ≺ d`. -/
def SeriesParallel {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ a b c d, Relation.TransGen r a c → Relation.TransGen r b c → Relation.TransGen r b d →
    Relation.TransGen r a d ∨ Relation.TransGen r a b ∨ Relation.TransGen r b a ∨
      Relation.TransGen r c d ∨ Relation.TransGen r d c

/-- The arcs among a set of jobs form a divide-and-conquer graph. -/
inductive DivideAndConquer {n : ℕ} (r : Fin n → Fin n → Prop) : Finset (Fin n) → Prop
  | single (v : Fin n) : ¬ r v v → DivideAndConquer r {v}
  | compose (s t : Fin n) (parts : List (Finset (Fin n))) :
      s ≠ t → parts ≠ [] → (∀ P ∈ parts, s ∉ P ∧ t ∉ P) → parts.Pairwise Disjoint →
      (∀ P ∈ parts, DivideAndConquer r P) →
      (∀ a b, (a = s ∨ a = t ∨ ∃ P ∈ parts, a ∈ P) → (b = s ∨ b = t ∨ ∃ P ∈ parts, b ∈ P) →
        (r a b ↔ (∃ P ∈ parts, a ∈ P ∧ b ∈ P ∧ r a b) ∨ (a = s ∧ ∃ P ∈ parts, b ∈ P) ∨
          (b = t ∧ ∃ P ∈ parts, a ∈ P))) →
      DivideAndConquer r (parts.foldr (· ∪ ·) {s, t})

/-- `a ≺ b` and `c ≺ d` imply `a ≺ d` or `c ≺ b`. -/
def IntervalOrder {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ a b c d, Relation.TransGen r a b → Relation.TransGen r c d →
    Relation.TransGen r a d ∨ Relation.TransGen r c b

/-- Five different jobs are related exactly by the pairs of a pattern. -/
def Contains {n : ℕ} (r : Fin n → Fin n → Prop) (pattern : List (Fin 5 × Fin 5)) : Prop :=
  ∃ f : Fin 5 → Fin n, Function.Injective f ∧
    ∀ a b, Relation.TransGen r (f a) (f b) ↔ (a, b) ∈ pattern
/-- Two unrelated pairs, the first job of one having a further successor. -/
def patternOut : List (Fin 5 × Fin 5) := [(0, 1), (2, 3), (2, 4)]
/-- The reverse of `patternOut`. -/
def patternIn : List (Fin 5 × Fin 5) := [(1, 0), (3, 2), (4, 2)]
/-- The third pattern forbidden in a quasi-interval order. -/
def patternThird : List (Fin 5 × Fin 5) := [(0, 1), (0, 3), (2, 3), (2, 4), (4, 3)]
/-- Neither `patternOut` nor its reverse occurs. -/
def OverInterval {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ¬ Contains r patternOut ∧ ¬ Contains r patternIn
/-- An over-interval order in which `patternThird` does not occur. -/
def QuasiInterval {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  OverInterval r ∧ ¬ Contains r patternThird
/-- Moukrim and Quilliot's property `Q_m`: for two sets of at most `m` pairwise
unrelated jobs, at most `m` jobs of their union have a predecessor in the union,
and at most `m` have a successor in the union. -/
def AOrder {n : ℕ} (m : ℕ) (r : Fin n → Fin n → Prop) : Prop :=
  ∀ A B : Finset (Fin n), (∀ x ∈ A, ∀ y ∈ A, ¬ Relation.TransGen r x y) →
    (∀ x ∈ B, ∀ y ∈ B, ¬ Relation.TransGen r x y) → A.card ≤ m → B.card ≤ m →
    ∀ U ⊆ A ∪ B,
      ((∀ x ∈ U, ∃ y ∈ A ∪ B, Relation.TransGen r y x) → U.card ≤ m) ∧
      ((∀ x ∈ U, ∃ y ∈ A ∪ B, Relation.TransGen r x y) → U.card ≤ m)
/-- A path of `l` arcs starts from the job. -/
def HasPath {n : ℕ} (r : Fin n → Fin n → Prop) : ℕ → Fin n → Prop
  | 0, _ => True
  | l + 1, v => ∃ w, r v w ∧ HasPath r l w

/-- The longest path of arcs starting from the job has `l` arcs. -/
def HasLevel {n : ℕ} (r : Fin n → Fin n → Prop) (v : Fin n) (l : ℕ) : Prop :=
  HasPath r l v ∧ ¬ HasPath r (l + 1) v

/-- Every job of level `l + 1` precedes every job of level `l`. -/
def LevelOrder {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ u v l, HasLevel r u (l + 1) → HasLevel r v l → Relation.TransGen r u v

/-- The jobs can be placed in `k`-dimensional space such that, for different
jobs, `i ≺ j` exactly if every coordinate of `i` is at most that of `j`. -/
def HasDimension {n : ℕ} (k : ℕ) (r : Fin n → Fin n → Prop) : Prop :=
  ∃ f : Fin n → Fin k → ℚ, ∀ i j, i ≠ j → (Relation.TransGen r i j ↔ ∀ c, f i c ≤ f j c)

/-- The relations of a class, for a number `m` of machines. -/
def Order.InClass {n : ℕ} (m : ℕ) : Order → (Fin n → Fin n → Prop) → Prop
  | .none, r => ∀ i j, ¬ r i j
  | .chains, r => AtMostOneSuccessor r ∧ AtMostOnePredecessor r
  | .intree, r => AtMostOneSuccessor r
  | .outtree, r => AtMostOnePredecessor r
  | .tree, r => AtMostOneSuccessor r ∨ AtMostOnePredecessor r
  | .opposingForest, r => OpposingForest r
  | .seriesParallel, r => SeriesParallel r
  | .divideAndConquer, r => DivideAndConquer r Finset.univ
  | .intervalOrder, r => IntervalOrder r
  | .quasiInterval, r => QuasiInterval r
  | .overInterval, r => OverInterval r
  | .aOrder, r => AOrder m r
  | .levelOrder, r => LevelOrder r
  | .boundedHeight, _ => True
  | .dimensionTwo, r => HasDimension 2 r
  | .boundedDimension, r => ∃ k, HasDimension k r
  | .prec, _ => True

def Order.le : Order → Order → Bool
  | _, .prec => true
  | .none, .divideAndConquer => false
  | .none, _ => true
  | .chains, .chains | .chains, .intree | .chains, .outtree | .chains, .tree
  | .chains, .opposingForest => true
  | .intree, .intree | .intree, .tree | .intree, .opposingForest => true
  | .outtree, .outtree | .outtree, .tree | .outtree, .opposingForest => true
  | .tree, .tree | .tree, .opposingForest => true
  | .chains, .seriesParallel | .intree, .seriesParallel | .outtree, .seriesParallel
  | .tree, .seriesParallel | .opposingForest, .seriesParallel => true
  | .chains, .dimensionTwo | .intree, .dimensionTwo | .outtree, .dimensionTwo
  | .tree, .dimensionTwo | .opposingForest, .dimensionTwo => true
  | .chains, .boundedDimension | .intree, .boundedDimension | .outtree, .boundedDimension
  | .tree, .boundedDimension | .opposingForest, .boundedDimension => true
  | .dimensionTwo, .boundedDimension => true
  | .intervalOrder, .quasiInterval | .intervalOrder, .overInterval | .intervalOrder, .aOrder
  | .quasiInterval, .overInterval => true
  | .seriesParallel, .dimensionTwo | .seriesParallel, .boundedDimension => true
  | v, w => decide (v = w)

def Order.embed {n : ℕ} : {v w : Order} → Order.le v w = true → v.Data n → w.Data n
  | _, .none, _, _ => ()
  | v, .chains, _, d | v, .intree, _, d | v, .outtree, _, d | v, .tree, _, d
  | v, .opposingForest, _, d | v, .seriesParallel, _, d | v, .divideAndConquer, _, d
  | v, .intervalOrder, _, d | v, .quasiInterval, _, d | v, .overInterval, _, d | v, .aOrder, _, d
  | v, .levelOrder, _, d
  | v, .boundedHeight, _, d | v, .dimensionTwo, _, d | v, .boundedDimension, _, d
  | v, .prec, _, d => v.view d

inductive Lags
  | zero
  | unit
  | constant
  | constantNonpositive
  | constantPositive
  | arbitrary
  | arbitraryNonpositive
  | arbitraryPositive
  deriving DecidableEq

/-- The data of a kind of lags. -/
def Lags.Data (n : ℕ) : Lags → Type
  | .zero | .unit => Unit
  | .constant | .constantNonpositive | .constantPositive => ℤ
  | .arbitrary | .arbitraryNonpositive | .arbitraryPositive => Fin n → Fin n → ℤ

/-- The lag between two jobs. -/
def Lags.view {n : ℕ} : (v : Lags) → v.Data n → Fin n → Fin n → ℤ
  | .zero, _ => fun _ _ => 0
  | .unit, _ => fun _ _ => 1
  | .constant, l | .constantNonpositive, l | .constantPositive, l => fun _ _ => l
  | .arbitrary, l | .arbitraryNonpositive, l | .arbitraryPositive, l => l

/-- The sign condition of a kind of lags. -/
def Lags.Admits {n : ℕ} : Lags → (Fin n → Fin n → ℤ) → Prop
  | .constantNonpositive, l | .arbitraryNonpositive, l => ∀ i j, l i j ≤ 0
  | .constantPositive, l | .arbitraryPositive, l => ∀ i j, 0 < l i j
  | _, _ => True

def Lags.le : Lags → Lags → Bool
  | .zero, .zero | .zero, .constant | .zero, .constantNonpositive | .zero, .arbitrary
  | .zero, .arbitraryNonpositive => true
  | .unit, .unit | .unit, .constant | .unit, .constantPositive | .unit, .arbitrary
  | .unit, .arbitraryPositive => true
  | .constant, .constant | .constant, .arbitrary => true
  | .constantNonpositive, .constantNonpositive | .constantNonpositive, .constant
  | .constantNonpositive, .arbitraryNonpositive | .constantNonpositive, .arbitrary => true
  | .constantPositive, .constantPositive | .constantPositive, .constant
  | .constantPositive, .arbitraryPositive | .constantPositive, .arbitrary => true
  | .arbitrary, .arbitrary => true
  | .arbitraryNonpositive, .arbitraryNonpositive | .arbitraryNonpositive, .arbitrary => true
  | .arbitraryPositive, .arbitraryPositive | .arbitraryPositive, .arbitrary => true
  | _, _ => false

def Lags.embed {n : ℕ} : {v w : Lags} → Lags.le v w = true → v.Data n → w.Data n
  | _, .zero, _, _ | _, .unit, _, _ => ()
  | .constant, .constant, _, l | .constantNonpositive, .constant, _, l
  | .constantPositive, .constant, _, l
  | .constantNonpositive, .constantNonpositive, _, l
  | .constantPositive, .constantPositive, _, l => l
  | .zero, .constant, _, _ | .zero, .constantNonpositive, _, _ => (0 : ℤ)
  | .unit, .constant, _, _ | .unit, .constantPositive, _, _ => (1 : ℤ)
  | v, .arbitrary, _, d | v, .arbitraryNonpositive, _, d | v, .arbitraryPositive, _, d =>
      v.view d
  | .zero, .constantPositive, h, _ | .unit, .constantNonpositive, h, _
  | .constant, .constantNonpositive, h, _ | .constant, .constantPositive, h, _
  | .constantNonpositive, .constantPositive, h, _
  | .constantPositive, .constantNonpositive, h, _
  | .arbitrary, .constant, h, _ | .arbitrary, .constantNonpositive, h, _
  | .arbitrary, .constantPositive, h, _ | .arbitraryNonpositive, .constant, h, _
  | .arbitraryNonpositive, .constantNonpositive, h, _
  | .arbitraryNonpositive, .constantPositive, h, _ | .arbitraryPositive, .constant, h, _
  | .arbitraryPositive, .constantNonpositive, h, _
  | .arbitraryPositive, .constantPositive, h, _ => absurd h Bool.false_ne_true

/-- A value of the field: a class of relations and a kind of lags. -/
structure Value where
  order : Order
  lags : Lags := .zero

/-- No precedence constraints. -/
def Value.none : Value := ⟨.none, .zero⟩

/-- The field of precedence constraints with time lags over a kernel with a
number of machines. -/
def module (K : Kernel) (machines : K.Inst → ℕ) : Module K where
  Value := Value
  Data v x := v.order.Data (K.jobs x) × v.lags.Data (K.jobs x)
  admits v x d := v.order.InClass (machines x) (v.order.view d.1) ∧ v.lags.Admits (v.lags.view d.2)
  constraint v x d σ := ∀ i j, v.order.view d.1 i j →
    (K.completion x σ i : ℚ) + (v.lags.view d.2 i j : ℚ) ≤ (K.start x σ j : ℚ)
  le v w := Order.le v.order w.order && Lags.le v.lags w.lags
  embed {v w} h _ d :=
    (Order.embed (v := v.order) (w := w.order) (Bool.and_eq_true_iff.mp h).1 d.1,
      Lags.embed (v := v.lags) (w := w.lags) (Bool.and_eq_true_iff.mp h).2 d.2)

axiom sound (K : Kernel) (machines : K.Inst → ℕ) : (module K machines).Sound

/-- The field of precedence constraints on one machine, without `A_m`-orders:
the value `A_m` admits no instance and lies below no other value. -/
def oneMachine (K : Kernel) : Module K where
  Value := Value
  Data := (module K fun _ => 1).Data
  admits v x d := v.order ≠ .aOrder ∧ (module K fun _ => 1).admits v x d
  constraint := (module K fun _ => 1).constraint
  le v w := (module K fun _ => 1).le v w && (w.order != .aOrder || v.order == .aOrder)
  embed {v w} h x d := (module K fun _ => 1).embed (v := v) (w := w)
    (Bool.and_eq_true_iff.mp h).1 x d

axiom oneMachine_sound (K : Kernel) : (oneMachine K).Sound

end Lax434175.Precedence
