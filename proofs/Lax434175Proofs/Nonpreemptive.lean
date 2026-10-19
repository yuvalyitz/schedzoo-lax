import Mathlib.Tactic
import Lax434175.Nonpreemptive

namespace Lax434175Proofs.Nonpreemptive
open Lax434175.Kernels Lax434175.ParallelMachines Lax434175.Nonpreemptive

/--
---
conclusion: Lax434175.Nonpreemptive.startsBeforeCompletion
---
-/
theorem startsBeforeCompletion : kernel.StartsBeforeCompletion := by
  intro x σ _ j
  change ((σ.start j : ℕ) : NNRat) ≤ ((completion x σ j : ℕ) : NNRat)
  exact_mod_cast Nat.le_add_right _ _

end Lax434175Proofs.Nonpreemptive
