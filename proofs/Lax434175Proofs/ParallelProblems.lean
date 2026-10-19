import Lax434175.ParallelProblems
import Lax434175Proofs.Assembly
import Lax434175Proofs.Counts
import Lax434175Proofs.ReleaseDates
import Lax434175Proofs.Deadlines
import Lax434175Proofs.Precedence
import Lax434175Proofs.Objectives
import Lax434175Proofs.ParallelMachines
import Lax434175Proofs.MachineSets
import Lax434175Proofs.CommunicationDelays
import Lax434175Proofs.Servers
import Lax434175Proofs.ForbiddenTimes
import Lax434175Proofs.Thresholds

namespace Lax434175Proofs.ParallelProblems
open Lax434175.Problems Lax434175.Assembly Lax434175.ParallelProblems
open Lax434175

/--
---
conclusion: Lax434175.ParallelProblems.family_sound
---
-/
theorem family_sound (M : ParallelMachines.Model) : (family M).Sound where
  module i := by
    cases i
    · exact ParallelMachines.environment_sound M
    · exact Counts.sound _ _
    · exact Counts.sound _ _
    · exact ParallelMachines.processingTimes_sound M
    · exact MachineSets.sound M
    · exact ReleaseDates.sound _
    · exact Deadlines.sound _
    · exact Precedence.sound _ _
    · exact CommunicationDelays.sound M
    · exact Servers.parallel_sound M
    · exact ForbiddenTimes.sound _
    · exact ForbiddenTimes.encoding_sound _
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.ParallelProblems.specialCase_of_le
---
-/
theorem specialCase_of_le (M : ParallelMachines.Model) {s t : Spec (family M)} :
    s.le t → SpecialCase (problem (family M) s) (problem (family M) t) :=
  fun h => ⟨lift (family M) (family_sound M) h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.ParallelProblems.reducible_of_reduces
---
-/
theorem reducible_of_reduces (M : ParallelMachines.Model) {s t : Spec (family M)} :
    Thresholds.Reduces s t → Reducible (problem (family M) s) (problem (family M) t) :=
  Thresholds.reducible_of_reduces (family_sound M).module

/--
---
conclusion: Lax434175.ParallelProblems.reducible_of_reducesThroughFlow
---
A job starts no earlier than its release date and completes no earlier than
it starts.
-/
theorem reducible_of_reducesThroughFlow (M : ParallelMachines.Model)
    (h : M.kernel.StartsBeforeCompletion) {s t : Spec (family M)} :
    Thresholds.ReducesThroughFlow s t → Reducible (problem (family M) s) (problem (family M) t) :=
  Thresholds.reducible_of_reducesThroughFlow (family_sound M).module
    (fun _ x _ σ _ hf hc j => le_trans (hc FieldName.releaseDates j) (h x σ hf j))

/--
---
conclusion: Lax434175.ParallelProblems.single_sumC_specialCase
---
The two specifications compare field by field.
-/
theorem single_sumC_specialCase :
    SpecialCase (problem nonpreemptive single_sumC)
      (problem nonpreemptive unrelated_release_prec_sumWT) :=
  specialCase_of_le _ (by decide)

end Lax434175Proofs.ParallelProblems
