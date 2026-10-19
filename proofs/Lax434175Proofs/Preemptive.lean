import Mathlib.Tactic
import Lax434175.Preemptive

namespace Lax434175Proofs.Preemptive
open Lax434175.Kernels Lax434175.ParallelMachines Lax434175.Preemptive

/-- The least element of a list of times is at most each of them. -/
theorem min_getD_le (l : List NNRat) (a : NNRat) (h : a ∈ l) : (l.min?).getD 0 ≤ a := by
  cases hm : l.min? with
  | none =>
    rw [List.min?_eq_none_iff] at hm
    subst hm
    simp at h
  | some b => exact (List.min?_eq_some_iff.mp hm).2 a h

/-- Each of a list of times is at most the greatest of them. -/
theorem le_max_getD (l : List NNRat) (a : NNRat) (h : a ∈ l) : a ≤ (l.max?).getD 0 := by
  cases hm : l.max? with
  | none =>
    rw [List.max?_eq_none_iff] at hm
    subst hm
    simp at h
  | some b => exact (List.max?_eq_some_iff.mp hm).2 a h

/-- A piece starts no later than it ends. -/
theorem start_le_finish {x : Inst} (q : Piece x) : q.start ≤ q.finish := by
  unfold Piece.finish
  exact le_self_add

/--
---
conclusion: Lax434175.Preemptive.startsBeforeCompletion
---
-/
theorem startsBeforeCompletion : kernel.StartsBeforeCompletion := by
  intro x σ _ j
  change (((piecesOf σ j).map Piece.start).min?).getD 0 ≤
    (((piecesOf σ j).map Piece.finish).max?).getD 0
  cases hL : piecesOf σ j with
  | nil => simp
  | cons q L =>
    have h1 := min_getD_le ((q :: L).map Piece.start) q.start (by simp)
    have h2 := le_max_getD ((q :: L).map Piece.finish) q.finish (by simp)
    exact le_trans h1 (le_trans (start_le_finish q) h2)

end Lax434175Proofs.Preemptive
