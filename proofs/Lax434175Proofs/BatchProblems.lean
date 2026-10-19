import Lax434175.BatchProblems
import Lax434175Proofs.Assembly
import Lax434175Proofs.Counts
import Lax434175Proofs.ReleaseDates
import Lax434175Proofs.Deadlines
import Lax434175Proofs.Precedence
import Lax434175Proofs.Objectives
import Lax434175Proofs.Thresholds
import Lax434175Proofs.Batching

namespace Lax434175Proofs.BatchProblems
open Lax434175.Problems Lax434175.Assembly Lax434175.BatchProblems
open Lax434175

/--
---
conclusion: Lax434175.BatchProblems.family_sound
---
-/
theorem family_sound (mode : Batching.Mode) : (family mode).Sound where
  module i := by
    cases i
    · exact Batching.capacity_sound mode
    · exact Counts.sound _ _
    · exact Batching.processingTimes_sound mode
    · exact ReleaseDates.sound _
    · exact Deadlines.sound _
    · exact Precedence.oneMachine_sound _
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.BatchProblems.specialCase_of_le
---
-/
theorem specialCase_of_le (mode : Batching.Mode) {s t : Spec (family mode)} :
    s.le t → SpecialCase (problem (family mode) s) (problem (family mode) t) :=
  fun h => ⟨lift (family mode) (family_sound mode) h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.BatchProblems.reducible_of_reduces
---
-/
theorem reducible_of_reduces (mode : Batching.Mode) {s t : Spec (family mode)} :
    Thresholds.Reduces s t → Reducible (problem (family mode) s) (problem (family mode) t) :=
  Thresholds.reducible_of_reduces (family_sound mode).module

end Lax434175Proofs.BatchProblems
