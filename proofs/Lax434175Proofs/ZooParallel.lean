import Lax434175.ZooParallel
import Lax434175Proofs.OperationsFamily

namespace Lax434175Proofs.ZooParallel
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.ZooParallel

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
conclusion: Lax434175.ZooParallel.specialCases_hold
---
-/
theorem specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1) :=
  fun e he => OperationsFamily.specialCase_of_le (specialCases_le e he)

/--
---
conclusion: Lax434175.ZooParallel.thresholdReductions_hold
---
-/
theorem thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1) :=
  fun e he => OperationsFamily.reducible_of_reduces (thresholdReductions_reduce e he)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Every listed pair reduces through flow time. -/
theorem flowReductions_reduce : ∀ e ∈ flowReductions,
    Thresholds.ReducesThroughFlow e.2 e.1 := by decide

/--
---
conclusion: Lax434175.ZooParallel.flowReductions_hold
---
-/
theorem flowReductions_hold : ∀ e ∈ flowReductions,
    Reducible (problem F e.2) (problem F e.1) :=
  fun e he => OperationsFamily.reducible_of_reducesThroughFlow (flowReductions_reduce e he)

end Lax434175Proofs.ZooParallel
