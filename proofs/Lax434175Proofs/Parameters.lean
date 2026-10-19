import Lax434175.Parameters

namespace Lax434175Proofs.Parameters
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.Parameters

/--
---
conclusion: Lax434175.Parameters.lift_ofKernel
---
-/
theorem lift_ofKernel {K : Kernel} (F : Family K) (hF : F.Sound) (κ : K.Inst → ℕ)
    {s t : Spec F} (h : s.le t) :
    ∀ x, ofKernel F κ t ((lift F hF h).map x) = ofKernel F κ s x :=
  fun _ => rfl

/--
---
conclusion: Lax434175.Parameters.lift_ofField
---
-/
theorem lift_ofField {K : Kernel} (F : Family K) (hF : F.Sound) (i : F.ModuleName)
    (κ : FieldParameter (F.module i)) (hκ : κ.Invariant) {s t : Spec F} (h : s.le t) :
    ∀ x, ofField F i κ t ((lift F hF h).map x) = ofField F i κ s x :=
  fun x => hκ _ _ (h.1 i) x.base (x.data i)

/--
---
conclusion: Lax434175.Parameters.reducibleWith_of_embedding
---
-/
theorem reducibleWith_of_embedding {A B : Problem} {α β : Type} (e : Embedding A B)
    (κA : A.Inst → α) (κB : B.Inst → β) (R : α → β → Prop) :
    e.Sound → (∀ x, R (κA x) (κB (e.map x))) → ReducibleWith κA κB R := by
  intro he hR
  refine ⟨⟨fun x _ => e.map x, fun _ D => D⟩, fun x D => ⟨?_, ?_⟩, fun x _ => hR x⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨e.forth x σ, he.forth_feasible x σ hf, le_trans (he.forth_cost x σ hf) hc⟩
  · rintro ⟨τ, hf, hc⟩
    exact ⟨e.back x τ, he.back_feasible x τ hf, le_trans (he.back_cost x τ hf) hc⟩

/--
---
conclusion: Lax434175.Parameters.reducibleWith_trans
---
-/
theorem reducibleWith_trans {A B C : Problem} {α β γ : Type} (κA : A.Inst → α)
    (κB : B.Inst → β) (κC : C.Inst → γ) (R : α → β → Prop) (S : β → γ → Prop) :
    ReducibleWith κA κB R → ReducibleWith κB κC S →
      ReducibleWith κA κC (fun a c => ∃ b, R a b ∧ S b c) := by
  rintro ⟨f, hf, pf⟩ ⟨g, hg, pg⟩
  exact ⟨⟨fun x D => g.map (f.map x D) (f.threshold x D),
    fun x D => g.threshold (f.map x D) (f.threshold x D)⟩,
    fun x D => (hf x D).trans (hg _ _), fun x D => ⟨_, pf x D, pg _ _⟩⟩

/--
---
conclusion: Lax434175.Parameters.reducible_of_reducibleWith
---
-/
theorem reducible_of_reducibleWith {A B : Problem} {α β : Type} (κA : A.Inst → α)
    (κB : B.Inst → β) (R : α → β → Prop) : ReducibleWith κA κB R → Reducible A B :=
  fun ⟨r, hr, _⟩ => ⟨r, hr⟩

end Lax434175Proofs.Parameters
