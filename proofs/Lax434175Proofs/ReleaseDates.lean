import Lax434175.ReleaseDates

namespace Lax434175Proofs.ReleaseDates
open Lax434175.Kernels Lax434175.Modules Lax434175.ReleaseDates

/--
---
conclusion: Lax434175.ReleaseDates.sound
---
-/
theorem sound (K : Kernel) : (module K).Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : Value) h x _ hv => by
    have hv' : v.holds K x := hv
    change w.holds K x
    cases v <;> cases w <;> first
      | exact absurd h Bool.false_ne_true
      | exact hv'
      | exact trivial

end Lax434175Proofs.ReleaseDates
