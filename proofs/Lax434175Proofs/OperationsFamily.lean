import Lax434175.OperationsFamily
import Lax434175Proofs.Operations
import Lax434175Proofs.ParallelFamily
import Lax434175Proofs.ShopFamily
import Lax434175Proofs.CommunicationDelays

namespace Lax434175Proofs.OperationsFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily

/--
---
conclusion: Lax434175.OperationsFamily.family_sound
---
-/
theorem family_sound : OperationsFamily.family.Sound where
  module
    | .interruption => Operations.interruption_sound
    | .jobStructure => Operations.jobStructure_sound
    | .environment => Operations.environment_sound
    | .machineCount => Counts.sound _ _
    | .jobCount => Counts.sound _ _
    | .processingTimes => Operations.processingTimes_sound
    | .machineSets => Operations.machineSets_sound
    | .releaseDates => ReleaseDates.sound _
    | .deadlines => Deadlines.sound _
    | .precedence => Precedence.sound _ _
    | .communicationDelays => CommunicationDelays.sound _
    | .server => Operations.server_sound
    | .forbiddenTimes => ForbiddenTimes.sound _
    | .encoding => ForbiddenTimes.encoding_sound _
    | .noWait => Operations.noWait_sound
    | .transportation => Operations.transportation_sound
    | .noIdle => Operations.noIdle_sound
    | .batchSetups => Operations.batchSetups_sound
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.OperationsFamily.specialCase_of_le
---
-/
theorem specialCase_of_le {s t : Spec OperationsFamily.family} :
    s.le t → SpecialCase (problem OperationsFamily.family s) (problem OperationsFamily.family t) :=
  fun h => ⟨lift OperationsFamily.family family_sound h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.OperationsFamily.reducible_of_reduces
---
-/
theorem reducible_of_reduces {s t : Spec OperationsFamily.family} :
    Thresholds.Reduces s t →
      Reducible (problem OperationsFamily.family s) (problem OperationsFamily.family t) :=
  Thresholds.reducible_of_reduces family_sound.module

/--
---
conclusion: Lax434175.OperationsFamily.reducible_of_reducesThroughFlow
---
A job starts no earlier than its release date and completes no earlier than
it starts.
-/
theorem reducible_of_reducesThroughFlow {s t : Spec OperationsFamily.family} :
    Thresholds.ReducesThroughFlow s t →
      Reducible (problem OperationsFamily.family s) (problem OperationsFamily.family t) :=
  Thresholds.reducible_of_reducesThroughFlow family_sound.module
    (fun _ x _ σ _ hf hc j => le_trans (hc .releaseDates j)
      (Operations.startsBeforeCompletion x σ hf j))

end Lax434175Proofs.OperationsFamily
