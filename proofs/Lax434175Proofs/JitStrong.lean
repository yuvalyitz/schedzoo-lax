import Mathlib.Tactic
import Lax434175.JitFlowShopStandard
import Lax434175Proofs.JitEmit
import Lax434175Proofs.JitSmall
import Lax496464.HittingSetHardness
import Lax759944.TuringRamPolytimeEquivalence
import Lax888481Proofs.TMCompose
import Lax888481Proofs.TMToNats
import Lax496464.WH_A5_Bridges

/-!
`FF(1,m)||ΣZ_j` is strongly NP-hard under the standard reading: every language in NP reduces to
Hitting Set (lax-496464) by a Turing machine writing the binary word of the instance; the bits are
turned into numbers (`TMToNats` of lax-888481), the numbers of the instance are read (`JitParse`)
and the standard word of the construction is written (`JitEmit`). Its numbers are at most
`64 (|w| + 1)^4` (`JitSmall`).
-/

namespace Lax434175Proofs.JitStrong
open Lax434175 Lax434175.Results Lax434175.JitFlowShop Lax434175.JitFlowShopStandard
open Lax434175Proofs.JitRaw Lax434175Proofs.JitWords Lax434175Proofs.JitParse
open Lax496464 Lax496464.HittingSet Lax496464.Construction
open Lax888481Proofs.Theorem2Assembly (natBits)

theorem toks_eq (P : HittingSet.Instance) (k : ℕ) : toks P k = tokens P k := rfl

/--
---
conclusion: Lax434175.JitFlowShopStandard.wordMap
---
The emitter's program: it checks the numbers, walks them once storing the membership pairs, and
writes the jobs of the construction one by one.
-/
theorem wordMap : ∃ F : List ℕ → List ℕ, Lax496464.WH_A1_FptTime.PolyTimeOn Set.univ F ∧
    ∀ (P : HittingSet.Instance) (k : ℕ), k ≤ P.n → P.n ≤ (tokens P k).length + 4 →
      EncodesDecision (StandardReading.ops.at ZooShops.p315) (F (tokens P k))
        (toZooUnit (construct P k)) ((numJobs P k : ℤ) - target P k) := by
  refine ⟨emitF, (Lax496464.WH_A5_Bridges.polyTimeOn_univ_iff _).mpr
    Lax434175Proofs.JitEmit.emitF_polytime, fun P k hk hn => ?_⟩
  rw [← toks_eq, emitF_toks P k hk hn]
  exact encodesDecision _ _

theorem standard_p315 : ZooShops.p315.module .encoding = .standard := rfl

/-- The answer of the emitted word. -/
theorem yes_iff (P : HittingSet.Instance) (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ P.n)
    {w : List ℕ} (hw : EncodesDecision (StandardReading.ops.at ZooShops.p315) w
      (toZooUnit (construct P k)) ((numJobs P k : ℤ) - target P k)) :
    (decision (StandardReading.ops.at ZooShops.p315)).Yes w ↔ P.HasHittingSet k := by
  rw [Theorem1.construct_correct P k hk hkn,
    Lax434175Proofs.JitFlowShop.hasWeight_iff_unit (construct P k) (by show 0 < k; omega)
      (fun _ => rfl)]
  constructor
  · rintro ⟨y, D, hy, hd⟩
    obtain ⟨hD, hi⟩ := Lax434175.Propagation.ops_determined standard_p315 w y _ D _ hy hw
    exact hi.mp hd
  · intro hd
    exact ⟨_, _, hw, hd⟩

/--
---
conclusion: Lax434175.JitFlowShopStandard.p315_r0_holds
---
Hitting Set (lax-496464), the numbers of its binary word, and the emitter, composed as Turing
machines; the numbers of the emitted word are at most `64 (|w| + 1)^4`.
-/
theorem p315_r0_holds : ZooShopsResults.p315_r0 StandardReading.ops := by
  show StronglyNPHard _
  refine ⟨64, 4, fun A hA => ?_⟩
  obtain ⟨f, c, ⟨tf⟩, hk, -, hn, hiff⟩ := HittingSetHardness.hittingSet_npHard A hA
  have tf' : Turing.TM2ComputableInPolyTime id id
      ((fun z : HittingSet.Instance × ℕ => encodeInstance z.1 z.2) ∘ f) :=
    ⟨tf.toTM2ComputableAux, tf.time, tf.outputsFun⟩
  obtain ⟨tN⟩ := Lax888481Proofs.TMToNats.toNats
  obtain ⟨tP⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    parseH_polytime
  obtain ⟨tE⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Lax434175Proofs.JitEmit.emitF_polytime
  obtain ⟨c1⟩ := Lax888481Proofs.TMCompose.comp tf' tN
  obtain ⟨c2⟩ := Lax888481Proofs.TMCompose.comp c1 tP
  obtain ⟨c3⟩ := Lax888481Proofs.TMCompose.comp c2 tE
  refine ⟨_, ⟨c3⟩, fun x => ?_⟩
  obtain ⟨hk2, hkn⟩ := hk x
  have hnx := hn x
  have hix := hiff x
  set P := (f x).1
  set k := (f x).2
  have hn' : P.n ≤ (toks P k).length + 4 := by
    have := toks_length P k; omega
  have hw : (emitF ∘ parseH ∘ natBits ∘ ((fun z : HittingSet.Instance × ℕ =>
      encodeInstance z.1 z.2) ∘ f)) x = stdWordJ (construct P k) ((numJobs P k : ℤ) - target P k) := by
    simp only [Function.comp]
    rw [parse_encode, emitF_toks P k hkn hn']
  have he := encodesDecision (construct P k) ((numJobs P k : ℤ) - target P k)
  refine ⟨⟨⟨_, _, hw ▸ he⟩, ?_⟩, ?_⟩
  · rw [hw, ← stdW_ofHS]
    exact Lax434175Proofs.JitSmall.small P k hk2 hkn hnx
  · rw [hix]
    exact (yes_iff P k hk2 hkn (hw ▸ he)).symm

end Lax434175Proofs.JitStrong
