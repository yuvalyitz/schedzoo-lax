import Lax434175.Counts

namespace Lax434175Proofs.Counts
open Lax434175.Kernels Lax434175.Modules Lax434175.Counts

/-- A more special bound admits fewer numbers. -/
theorem holds_mono (v w : Bound) (h : v.le w = true) (jobs n : ℕ) :
    v.holds jobs n → w.holds jobs n := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h Bool.false_ne_true
    | exact trivial
    | exact hv
    | exact Nat.le_trans hv (of_decide_eq_true h)

/--
---
conclusion: Lax434175.Counts.sound
---
-/
theorem sound (K : Kernel) (count : K.Inst → ℕ) {least : ℕ} : (module K count least).Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : Bound) h x _ hv => ⟨holds_mono v w h (K.jobs x) (count x) hv.1,
    fun k hk => by
      subst hk
      cases v <;> first
        | exact absurd h Bool.false_ne_true
        | exact hv.2 _ rfl⟩

end Lax434175Proofs.Counts
