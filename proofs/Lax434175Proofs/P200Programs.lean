import Mathlib.Tactic
import Lax434175Proofs.P200ProgramsSpec
import Lax434175Proofs.P200ProgramsParse
import Lax434175Proofs.P200ProgramsBuildB
import Lax888481Proofs.TMCompose
import Lax759944.TuringRamPolytimeEquivalence

/-!
The word map from the standard words of `P|M_j|Σ w_j Z_j` to the words of interval scheduling
of the padded scaled instance (`toIsemWord = buildWord ∘ parseWord`):

* `toIsemWord_spec` (in `P200ProgramsSpec`): when every job has a machine, the word of
  `stdWordR R D` is the padded scaled instance `pad R.toIsem` with threshold `(Σ w_j - D)⁺`;
* `toIsemWord_no` (in `P200ProgramsSpec`): otherwise it is `[0, 0, 0, 1]`;
* `toIsemWord_turing`: the map is polynomial on a Turing machine, composed from the two word
  RAM programs `parseWord_polytime` and `buildWord_polytime`.
-/

namespace Lax434175Proofs.P200Programs
open Lax759944.BinaryWordEncoding

/-- **The word map is polynomial on a Turing machine.** -/
theorem toIsemWord_turing : Nonempty (Turing.TM2ComputableInPolyTime encode encode toIsemWord) := by
  obtain ⟨t1⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    parseWord_polytime
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    buildWord_polytime
  exact Lax888481Proofs.TMCompose.comp t1 t2

end Lax434175Proofs.P200Programs
