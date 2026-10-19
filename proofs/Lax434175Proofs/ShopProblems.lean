import Lax434175.ShopProblems
import Lax434175Proofs.Assembly
import Lax434175Proofs.Counts
import Lax434175Proofs.ReleaseDates
import Lax434175Proofs.Deadlines
import Lax434175Proofs.Precedence
import Lax434175Proofs.Objectives
import Lax434175Proofs.Shops
import Lax434175Proofs.Transportation
import Lax434175Proofs.Servers
import Lax434175Proofs.ShopExtras
import Lax434175Proofs.Thresholds

namespace Lax434175Proofs.ShopProblems
open Lax434175.Problems Lax434175.Assembly Lax434175.ShopProblems
open Lax434175

/--
---
conclusion: Lax434175.ShopProblems.family_sound
---
-/
theorem family_sound : family.Sound where
  module i := by
    cases i
    · exact Shops.shopType_sound
    · exact Shops.machineSets_sound
    · exact Counts.sound _ _
    · exact Counts.sound _ _
    · exact Shops.processingTimes_sound
    · exact Shops.noWait_sound
    · exact Transportation.sound
    · exact Servers.shop_sound
    · exact ShopExtras.noIdle_sound
    · exact ShopExtras.batchSetups_sound
    · exact ReleaseDates.sound _
    · exact Deadlines.sound _
    · exact Precedence.sound _ _
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.ShopProblems.specialCase_of_le
---
-/
theorem specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t) :=
  fun h => ⟨lift family family_sound h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.ShopProblems.reducible_of_reduces
---
-/
theorem reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t) :=
  Thresholds.reducible_of_reduces family_sound.module

/--
---
conclusion: Lax434175.ShopProblems.flow2_makespan_specialCase
---
-/
theorem flow2_makespan_specialCase :
    SpecialCase (problem family flow2_makespan) (problem family job_release_lmax) :=
  specialCase_of_le (by decide)

end Lax434175Proofs.ShopProblems
