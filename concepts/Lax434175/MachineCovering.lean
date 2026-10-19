import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Lax434175.Problems

/-!
---
title: Maximizing the minimum machine load
type: definition
---
The problem $P \mid\mid C_{\min}$. An instance has $n$ jobs with processing
times $p_j$ and $m$ identical machines. A solution assigns every job to a
machine. The load of a machine is the sum of the processing times of its
jobs, and the goal is to maximize the smallest load.

As a minimization problem, the cost of an assignment is the negative of the
smallest load; without machines it is $0$.
-/

namespace Lax434175.MachineCovering
open Lax434175.Problems

structure Inst where
  jobs : ℕ
  machines : ℕ
  p : Fin jobs → ℕ

/-- The load of a machine. -/
def load (x : Inst) (σ : Fin x.jobs → Fin x.machines) (i : Fin x.machines) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), x.p j

/-- The smallest load of a machine; `0` without machines. -/
def minLoad (x : Inst) (σ : Fin x.jobs → Fin x.machines) : ℕ :=
  if h : 0 < x.machines then Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (load x σ) else 0

/-- `P || C_min` -/
def problem : Problem where
  Inst := Inst
  Sched x := Fin x.jobs → Fin x.machines
  feasible _ _ := True
  cost x σ := -(minLoad x σ : ℚ)

end Lax434175.MachineCovering
