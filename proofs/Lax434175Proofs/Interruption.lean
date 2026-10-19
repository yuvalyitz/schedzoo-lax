import Mathlib.Tactic
import Lax434175.Interruption
import Lax434175Proofs.Preemptive

namespace Lax434175Proofs.Interruption
open Lax434175.Kernels Lax434175.ParallelMachines Lax434175.Preemptive Lax434175.Interruption
open Lax434175

/--
---
conclusion: Lax434175.Interruption.sound
---
Two values are comparable only if they are equal.
-/
theorem sound : Interruption.module.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint v w h _ _ _ _ := by
    change Mode at v w
    cases v <;> cases w <;> first | exact Iff.rfl | exact absurd h (by decide)

/-- Pieces sent to pieces on the same machines: the pieces of a list occupy one
set of machines exactly when their images do. -/
theorem sameMachines_map {α β M : Type} (L : List α) (f : α → β) (ma : α → M) (mb : β → M)
    (hf : ∀ a, mb (f a) = ma a) :
    (∀ q ∈ L.map f, ∀ q' ∈ L.map f, mb q = mb q') ↔ ∀ q ∈ L, ∀ q' ∈ L, ma q = ma q' := by
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hf]

/--
---
conclusion: Lax434175.Interruption.startsBeforeCompletion
---
-/
theorem startsBeforeCompletion : Interruption.kernel.StartsBeforeCompletion := by
  intro x σ _ j
  change (((piecesOf σ j).map Piece.start).min?).getD 0 ≤
    (((piecesOf σ j).map Piece.finish).max?).getD 0
  cases hL : piecesOf σ j with
  | nil => simp
  | cons q L =>
    have h1 := Preemptive.min_getD_le ((q :: L).map Piece.start) q.start (by simp)
    have h2 := Preemptive.le_max_getD ((q :: L).map Piece.finish) q.finish (by simp)
    exact le_trans h1 (le_trans (Preemptive.start_le_finish q) h2)

end Lax434175Proofs.Interruption
