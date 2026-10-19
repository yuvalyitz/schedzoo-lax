import Mathlib.Tactic
import Lax434175Proofs.IsemWords
import Lax434175Proofs.PropagationParameters
import Lax434175.JitHardness
import Lax496464.WH_A5_Bridges
import Lax888481Proofs.TMCompose
import Lax759944.TuringRamPolytimeEquivalence
import Lax434175.IsemStandard
import Lax434175Proofs.IsemPrograms
import Lax434175Proofs.JitHardness
import Lax888481Proofs.Theorem2

/-!
The hardness results of `P|M_j|Σ w_j Z_j` on the words of interval scheduling, carried
to the zoo's problem `p200` under the standard reading.
-/

namespace Lax434175Proofs.IsemBridge
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.IsemLink
open Lax434175.ResultParameters
open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175Proofs.IsemStandard Lax434175Proofs.IsemWords Lax434175Proofs.IsemCompress
open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

/-- The word map: drop the unused machines, then write the standard word. -/
def isemToStd (x : List ℕ) : List ℕ := stdOfWord (compressWord x)

theorem isemToStd_encodes {x : List ℕ} {I : Instance} {W : ℕ} (hx : EncodesDecisionInstance x I W) :
    EncodesDecision (StandardReading.ops.at ZooParallel.p200) (isemToStd x) (opsOf (compress I))
      ((totalWeight I : ℤ) - W) := by
  obtain ⟨y0, rfl, hy0⟩ := hx
  obtain ⟨y1, h1, h2, h3⟩ := compressWord_eq (W := W) hy0
  unfold isemToStd
  rw [h1, stdOfWord_eq h2 (by simp; omega)]
  exact encodesDecision (compress I) W

theorem standard_p200 : ZooParallel.p200.module .encoding = .standard := rfl

theorem yes_iff {w : List ℕ} {y : Inst OperationsFamily.family ZooParallel.p200} {D : ℤ}
    (hw : EncodesDecision (StandardReading.ops.at ZooParallel.p200) w y D) :
    (decision (StandardReading.ops.at ZooParallel.p200)).Yes w ↔
      (problem _ ZooParallel.p200).Decides y D := by
  constructor
  · rintro ⟨y', D', hw', h⟩
    obtain ⟨-, hi⟩ := Lax434175.Propagation.ops_determined standard_p200 w y' y D' D hw' hw
    exact hi.mp h
  · exact fun h => ⟨y, D, hw, h⟩

theorem allEligible_compress {I : Instance} (h : AllEligible I) : AllEligible (compress I) := by
  intro j
  obtain ⟨i, hi⟩ := h j
  exact ⟨⟨rank I i, rank_lt (mem_used hi)⟩, mem_compress.mpr ⟨i, hi, rfl⟩⟩

/-- The answer is kept, when every job has an eligible machine. -/
theorem yes_isemToStd {x : List ℕ} {I : Instance} {W : ℕ} (hx : EncodesDecisionInstance x I W)
    (hI : AllEligible I) :
    (decision (StandardReading.ops.at ZooParallel.p200)).Yes (isemToStd x) ↔ I.HasWeight W := by
  rw [yes_iff (isemToStd_encodes hx), hasWeight_compress,
    hasWeight_iff_ops (compress I) (allEligible_compress hI) W]
  rfl

/-- With unit weights and threshold the total weight: every job schedulable. -/
theorem yes_isemToStd_all {x : List ℕ} {I : Instance} (hx : EncodesDecisionInstance x I (totalWeight I))
    (hw : ∀ j, I.w j = 1) :
    (decision (StandardReading.ops.at ZooParallel.p200)).Yes (isemToStd x) ↔ I.AllSchedulable := by
  rw [yes_iff (isemToStd_encodes hx), allSchedulable_compress,
    allSchedulable_iff_ops (compress I) hw]
  have e : (((totalWeight I : ℤ) - (totalWeight I : ℕ) : ℤ) : ℚ) = 0 := by simp
  rw [e]

theorem m_le {I : Instance} :
    Ops.m ZooParallel.p200 (opsOf (compress I)) ≤ I.machines := machines_compress_le

theorem pmax_le {I : Instance} (h : I.pmax ≤ 25) :
    Ops.pmax ZooParallel.p200 (opsOf (compress I)) ≤ 25 := by
  unfold Ops.pmax
  refine Finset.sup_le fun o _ => ?_
  unfold Operations.opTime
  split_ifs
  · exact le_trans (Finset.le_sup (f := I.p) (Finset.mem_univ o.1)) h
  · omega

open Lax759944.BinaryWordEncoding in
/-- The word map is polynomial on a Turing machine. -/
theorem isemToStd_turing : Nonempty (Turing.TM2ComputableInPolyTime encode encode isemToStd) := by
  obtain ⟨t1⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Lax434175Proofs.IsemPrograms.compressWord_polytime
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Lax434175Proofs.IsemPrograms.stdOfWord_polytime
  exact Lax888481Proofs.TMCompose.comp t1 t2

theorem p200_le : ZooParallel.p200.le ZooParallel.p200 := by decide

/-- **The fpt-reduction to the standard reading.** -/
theorem fptReduces_std : jitByMachines ≤ᶠᵖᵗ
    parameterized (StandardReading.ops.at ZooParallel.p200) (lift (Ops.m ZooParallel.p200)) := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_polyTime (R := isemToStd) ⟨fun x hx => ?_, fun x hx => ?_⟩
    ⟨id, Computable.id, fun x hx => ?_⟩
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_turingPolytime _ isemToStd_turing)
  · obtain ⟨I, W, hx, -⟩ := hx
    exact ⟨_, _, isemToStd_encodes hx⟩
  · obtain ⟨I, W, hx, hI⟩ := hx
    show (∃ I' W', EncodesDecisionInstance x I' W' ∧ _) ↔ (decision _).Yes (isemToStd x)
    rw [yes_isemToStd hx hI]
    constructor
    · rintro ⟨I', W', hx', h⟩
      obtain ⟨rfl, rfl⟩ := Lax434175Proofs.IsemLink.encodesDecision_unique hx hx'
      exact (hasWeight_iff I hI W).mpr h
    · exact fun h => ⟨I, W, hx, (hasWeight_iff I hI W).mp h⟩
  · classical
    obtain ⟨I, W, hx, -⟩ := hx
    have henc := isemToStd_encodes hx
    show (if h : ∃ y D, EncodesDecision (StandardReading.ops.at ZooParallel.p200) (isemToStd x) y D then
      lift (Ops.m ZooParallel.p200) h.choose h.choose_spec.choose else 0) ≤ machineCount x
    split_ifs with h
    · have hb := Lax434175.PropagationParameters.ops_m p200_le rfl rfl (isemToStd x) _ _ _ _ henc
        h.choose_spec.choose_spec
      obtain ⟨y0, rfl, hy0⟩ := hx
      rw [machineCount_eq hy0]
      exact hb.le.trans m_le
    · exact Nat.zero_le _

/--
---
conclusion: Lax434175.IsemStandard.wHard_m
---
Multicoloured Clique fpt-reduces to interval scheduling (lax-888481 and padding), and
interval scheduling to the standard reading: drop the unused machines, write the standard
word.
-/
theorem wHard_m : WHard (StandardReading.ops.at ZooParallel.p200) 1 (lift (Ops.m ZooParallel.p200)) :=
  Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces Lax434175.JitHardness.w1Hard_jitByMachines
    fptReduces_std

open Lax759944.BinaryWordEncoding Lax888481Proofs.Theorem2Assembly in
/--
---
conclusion: Lax434175.IsemStandard.paraNPHard_pmax
---
Tovey's theorem, Construction 2 of lax-888481 on words, the total weight as the threshold,
and the word map to the standard reading; the instances have processing times at most 25.
-/
theorem paraNPHard_pmax :
    ParaNPHard (StandardReading.ops.at ZooParallel.p200) (lift (Ops.pmax ZooParallel.p200)) := by
  refine ⟨25, fun A hA => ?_⟩
  obtain ⟨g, ⟨tg⟩, hg⟩ := Lax888481.SatVariant.sat34_npHard A hA
  let P := Lax888481Proofs.Theorem2.parts
  obtain ⟨t1⟩ := P.toNats
  obtain ⟨t2⟩ := turing_of_ram P.parse_time
  obtain ⟨t3⟩ := turing_of_ram Lax888481Proofs.Checker.reduce_ramPolytime
  obtain ⟨t4⟩ := turing_of_ram Lax434175Proofs.IsemPrograms.appendTotal_polytime
  obtain ⟨t5⟩ := isemToStd_turing
  obtain ⟨c12⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  obtain ⟨c13⟩ := Lax888481Proofs.TMCompose.comp c12 t3
  obtain ⟨c14⟩ := Lax888481Proofs.TMCompose.comp c13 t4
  obtain ⟨c15⟩ := Lax888481Proofs.TMCompose.comp c14 t5
  obtain ⟨c⟩ := Lax888481Proofs.TMCompose.comp tg c15
  refine ⟨_, ⟨c⟩, fun x => ?_⟩
  set z := P.parse (natBits (g x))
  obtain ⟨I, hI, hp, hw⟩ := Lax888481.Construction2.reduce_slice z
  have hx := Lax434175Proofs.IsemPrograms.appendTotal_encodes hI
  have henc := isemToStd_encodes hx
  refine ⟨⟨⟨_, _, henc⟩, ⟨_, _, henc, pmax_le hp⟩⟩, ?_⟩
  show x ∈ A ↔ (decision _).Yes (isemToStd (Lax434175Proofs.IsemPrograms.appendTotal
    (Lax888481.Construction2.reduce z)))
  rw [yes_isemToStd_all hx hw, hg x, P.parse_correct, Lax888481.Construction2.reduce_correct]
  constructor
  · rintro ⟨I', hI', h⟩
    rwa [Lax434175Proofs.IsemLink.encodesInstance_unique hI hI']
  · exact fun h => ⟨I, hI, h⟩

end Lax434175Proofs.IsemBridge
