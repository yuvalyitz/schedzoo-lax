import Lax434175.ShopExtras

namespace Lax434175Proofs.ShopExtras
open Lax434175.Kernels Lax434175.Modules Lax434175.Shops Lax434175.ShopExtras

/--
---
conclusion: Lax434175.ShopExtras.noIdle_sound
---
-/
theorem noIdle_sound : noIdle.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : NoIdle) h x _ σ _ => by
    have h' : v = w := of_decide_eq_true h
    subst h'
    exact Iff.rfl

/-- Reading batch setups with a more general value does not change the
batches. -/
theorem batch_embed (v w : BatchSetups) (h : BatchSetups.le v w = true) (x : Inst)
    (d : v.Data x) : w.batch (BatchSetups.embed h x d) = v.batch d := by
  cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | rfl

/-- Reading batch setups with a more general value does not change the
setup times. -/
theorem setup_embed (v w : BatchSetups) (h : BatchSetups.le v w = true) (x : Inst)
    (d : v.Data x) : w.setup (BatchSetups.embed h x d) = v.setup d := by
  cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | rfl

/--
---
conclusion: Lax434175.ShopExtras.batchSetups_sound
---
-/
theorem batchSetups_sound : batchSetups.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : BatchSetups) h (x : Inst) (d : v.Data x) σ _ => by
    dsimp only [batchSetups, Follows]
    rw [batch_embed v w h x d, setup_embed v w h x d]

end Lax434175Proofs.ShopExtras
