import Lax434175.Assembly

namespace Lax434175Proofs.Assembly
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

/--
---
conclusion: Lax434175.Assembly.lift_sound
---
The schedule is unchanged, so each claim reduces to the soundness of the
fields.
-/
theorem lift_sound {K : Kernel} (F : Family K) (hF : F.Sound) {s t : Spec F} (h : s.le t) :
    (lift F hF h).Sound where
  forth_feasible x σ hσ :=
    ⟨hσ.1, fun i => ((hF.module i).constraint _ _ (h.1 i) x.base (x.data i) σ (x.admitted i)).2 (hσ.2 i)⟩
  forth_cost x σ _ := le_of_eq (hF.objective.cost _ _ h.2 x.base x.objectiveData σ)
  back_feasible x τ hτ :=
    ⟨hτ.1, fun i => ((hF.module i).constraint _ _ (h.1 i) x.base (x.data i) τ (x.admitted i)).1 (hτ.2 i)⟩
  back_cost x τ _ := le_of_eq (hF.objective.cost _ _ h.2 x.base x.objectiveData τ).symm

end Lax434175Proofs.Assembly
