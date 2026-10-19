import Lax434175.PreemptiveShops
import Lax434175Proofs.Shops

namespace Lax434175Proofs.PreemptiveShops
open Lax434175.Kernels Lax434175.Modules Lax434175.Shops Lax434175.PreemptiveShops
open Lax434175

/--
---
conclusion: Lax434175.PreemptiveShops.shopType_sound
---
-/
theorem shopType_sound : PreemptiveShops.shopType.Sound where
  admits := fun (v w : ShopType) h x _ hv => Shops.shopType_holds_mono v w h x hv
  constraint := fun (v w : ShopType) h x _ σ _ => by
    change ordered w x σ ↔ ordered v x σ
    cases v <;> cases w <;> first
      | exact absurd h (by decide)
      | exact Iff.rfl

/--
---
conclusion: Lax434175.PreemptiveShops.machineSets_sound
---
-/
theorem machineSets_sound : PreemptiveShops.machineSets.Sound where
  admits := fun (v w : Machines) h x (d : v.Data x) hv =>
    Shops.machines_admits_mono v w h x d hv
  constraint := fun (v w : Machines) h x (d : v.Data x) _ hv =>
    forall_congr' fun q => forall_congr' fun _ =>
      Shops.machines_view_iff v w h x d hv q.op.1 q.op.2 q.machines

/--
---
conclusion: Lax434175.PreemptiveShops.processingTimes_sound
---
-/
theorem processingTimes_sound : PreemptiveShops.processingTimes.Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : ProcessingTimes) h x _ hv =>
    Shops.processingTimes_mono v w (of_decide_eq_true h) x hv

end Lax434175Proofs.PreemptiveShops
