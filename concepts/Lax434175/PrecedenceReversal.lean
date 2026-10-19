import Lax434175.Precedence

/-!
---
title: Reversing precedence constraints
type: theorem
---
Reversing a relation turns every arc $i \to j$ into $j \to i$. Reversal maps
intrees to outtrees and outtrees to intrees, and every other class of the
precedence field except quasi-interval orders, divide-and-conquer graphs and
level orders to itself; these three are called not reversible here.
Reversing the data of a value of the precedence field reverses the relation
and transposes arbitrary lags, $l'_{ij} = l_{ji}$; other lags are kept.

**Theorem.** For a reversible class, the reverse of a relation of the class
belongs to the reversed class; reversed lags satisfy the same sign
condition.
-/

namespace Lax434175.PrecedenceReversal
open Lax434175.Precedence

/-- The class of the reverses of the relations of a class. -/
def reverse : Order → Order
  | .intree => .outtree
  | .outtree => .intree
  | o => o

/-- The classes whose reverses are shown to stay in a class. -/
def reversible : Order → Bool
  | .quasiInterval | .divideAndConquer | .levelOrder => false
  | _ => true

/-- The reversed relation of a value. -/
def reverseData {n : ℕ} : (o : Order) → o.Data n → (reverse o).Data n
  | .none, _ => ()
  | .chains, r | .intree, r | .outtree, r | .tree, r | .opposingForest, r
  | .seriesParallel, r | .divideAndConquer, r | .intervalOrder, r | .quasiInterval, r
  | .overInterval, r | .aOrder, r | .levelOrder, r | .boundedHeight, r | .dimensionTwo, r
  | .boundedDimension, r | .prec, r => fun i j => r j i

/-- The transposed lags of a value. -/
def lagsReverseData {n : ℕ} : (l : Lags) → l.Data n → l.Data n
  | .arbitrary, d | .arbitraryNonpositive, d | .arbitraryPositive, d => fun i j => d j i
  | .zero, d | .unit, d | .constant, d | .constantNonpositive, d | .constantPositive, d => d

axiom view_reverse {n : ℕ} (o : Order) (d : o.Data n) (i j : Fin n) :
    (reverse o).view (reverseData o d) i j ↔ o.view d j i

axiom lags_view_reverse {n : ℕ} (l : Lags) (d : l.Data n) (i j : Fin n) :
    l.view (lagsReverseData l d) i j = l.view d j i

axiom inClass_reverse {n : ℕ} (m : ℕ) (o : Order) (h : reversible o = true)
    (r : Fin n → Fin n → Prop) : o.InClass m r → (reverse o).InClass m (fun i j => r j i)

axiom lags_admits_reverse {n : ℕ} (l : Lags) (d : l.Data n) :
    l.Admits (l.view d) → l.Admits (l.view (lagsReverseData l d))

end Lax434175.PrecedenceReversal
