import Lax434175.PreemptiveShopProblems
import Lax434175Proofs.Assembly
import Lax434175Proofs.Counts
import Lax434175Proofs.ReleaseDates
import Lax434175Proofs.Deadlines
import Lax434175Proofs.Precedence
import Lax434175Proofs.Objectives
import Lax434175Proofs.Thresholds
import Lax434175Proofs.PreemptiveShops

namespace Lax434175Proofs.PreemptiveShopProblems
open Lax434175.Problems Lax434175.Assembly Lax434175.PreemptiveShopProblems
open Lax434175

/--
---
conclusion: Lax434175.PreemptiveShopProblems.family_sound
---
-/
theorem family_sound : family.Sound where
  module i := by
    cases i
    · exact PreemptiveShops.shopType_sound
    · exact PreemptiveShops.machineSets_sound
    · exact Counts.sound _ _
    · exact Counts.sound _ _
    · exact PreemptiveShops.processingTimes_sound
    · exact ReleaseDates.sound _
    · exact Deadlines.sound _
    · exact Precedence.sound _ _
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.PreemptiveShopProblems.specialCase_of_le
---
-/
theorem specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t) :=
  fun h => ⟨lift family family_sound h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.PreemptiveShopProblems.reducible_of_reduces
---
-/
theorem reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t) :=
  Thresholds.reducible_of_reduces family_sound.module

end Lax434175Proofs.PreemptiveShopProblems
