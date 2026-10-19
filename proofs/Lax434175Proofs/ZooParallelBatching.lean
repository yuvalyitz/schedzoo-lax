import Lax434175.ZooParallelBatching
import Lax434175Proofs.BatchFamily

namespace Lax434175Proofs.ZooParallelBatching
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.ZooParallelBatching

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Every listed pair compares field by field. -/
theorem specialCases_le : ∀ e ∈ specialCases, e.2.le e.1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Every listed pair reduces after a threshold step. -/
theorem thresholdReductions_reduce : ∀ e ∈ thresholdReductions,
    Thresholds.Reduces e.2 e.1 := by decide

/--
---
conclusion: Lax434175.ZooParallelBatching.specialCases_hold
---
-/
theorem specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1) :=
  fun e he => BatchFamily.specialCase_of_le (specialCases_le e he)

/--
---
conclusion: Lax434175.ZooParallelBatching.thresholdReductions_hold
---
-/
theorem thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1) :=
  fun e he => BatchFamily.reducible_of_reduces (thresholdReductions_reduce e he)

end Lax434175Proofs.ZooParallelBatching
