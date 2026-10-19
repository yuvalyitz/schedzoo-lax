import Lax434175.ParallelMachines

namespace Lax434175Proofs.ParallelMachines
open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines

/-- A more special environment has fewer instances. -/
theorem environment_mono (v w : Environment) (h : v.rank ≤ w.rank) (x : Inst) :
    v.holds x → w.holds x := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | exact hv
    | exact trivial
    | skip
  refine ⟨fun j => if h : 0 < x.machines then x.p j ⟨0, h⟩ else 0, fun _ => 1, fun j i => ?_⟩
  have hpos : 0 < x.machines := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  simp only [hpos, dite_true, Nat.mul_one, Nat.lt_one_iff, true_and]
  exact hv j i _

/--
---
conclusion: Lax434175.ParallelMachines.environment_sound
---
Identical machines are uniform machines of speed one; the length of a job is
its processing time on any machine.
-/
theorem environment_sound (M : Model) : (environment M).Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : Environment) h x _ hv =>
    environment_mono v w (of_decide_eq_true h) (M.inst x) hv

/-- A more special processing-time restriction has fewer instances. -/
theorem processingTimes_mono (v w : ProcessingTimes) (h : ProcessingTimes.le v w = true)
    (x : Inst) : v.holds x → w.holds x := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | exact hv
    | exact trivial
    | exact ⟨1, hv⟩
    | exact fun j i => Or.inl (hv j i)

/--
---
conclusion: Lax434175.ParallelMachines.processingTimes_sound
---
-/
theorem processingTimes_sound (M : Model) : (processingTimes M).Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : ProcessingTimes) h x _ hv =>
    processingTimes_mono v w h (M.inst x) hv

end Lax434175Proofs.ParallelMachines
