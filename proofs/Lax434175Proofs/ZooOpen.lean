import Lax434175.ZooOpen
import Lax496464.WH_A3_ReductionCalculus

namespace Lax434175Proofs.ZooOpen
open Lax434175.Problems Lax434175.Results
open Lax496464.WH_A2_FptReductions Lax496464.WH_A3_ReductionCalculus

/--
---
conclusion: Lax434175.ZooOpen.exclusive_fpt
---
Every problem of W[t] reduces to the parameterized problem, which is in FPT.
-/
theorem exclusive_fpt {P : Problem} {R : PReading P} {κ : TParameter P} {t : ℕ} :
    IsFPT R κ → WHard R t κ →
      ∀ Q ∈ Lax496464.WH_B4_Hierarchies.W t, IsParameterized Q →
        Q ∈ Lax496464.WH_A2_FptReductions.FPT :=
  fun hf hw Q hQ hp => mem_FPT_of_fptReduces hp (hw Q hQ) hf

end Lax434175Proofs.ZooOpen
