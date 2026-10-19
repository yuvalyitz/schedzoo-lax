import Mathlib.Tactic
import Lax434175.Restarts
import Lax434175Proofs.Preemptive

namespace Lax434175Proofs.Restarts
open Lax434175.Kernels Lax434175.ParallelMachines Lax434175.Preemptive Lax434175.Restarts
open Lax434175

/--
---
conclusion: Lax434175.Restarts.startsBeforeCompletion
---
The first complete piece of a job is one of its pieces.
-/
theorem startsBeforeCompletion : Restarts.kernel.StartsBeforeCompletion := by
  intro x σ hf j
  change (((piecesOf σ j).map Piece.start).min?).getD 0 ≤
    (((completePieces σ j).map Piece.finish).min?).getD 0
  have hne : completePieces σ j ≠ [] := hf.2.2 j
  cases hm : ((completePieces σ j).map Piece.finish).min? with
  | none =>
    rw [List.min?_eq_none_iff, List.map_eq_nil_iff] at hm
    exact absurd hm hne
  | some b =>
    have hb : b ∈ (completePieces σ j).map Piece.finish := (List.min?_eq_some_iff.mp hm).1
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    have hq' : q ∈ piecesOf σ j := (List.mem_filter.mp hq).1
    have h1 := Preemptive.min_getD_le ((piecesOf σ j).map Piece.start) q.start
      (List.mem_map.mpr ⟨q, hq', rfl⟩)
    exact le_trans h1 (Preemptive.start_le_finish q)

end Lax434175Proofs.Restarts
