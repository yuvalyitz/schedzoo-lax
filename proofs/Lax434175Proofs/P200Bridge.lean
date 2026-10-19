import Mathlib.Tactic
import Lax434175Proofs.P200Decides
import Lax434175Proofs.P200Bound
import Lax434175Proofs.P200Programs
import Lax434175Proofs.P200Param
import Lax434175Proofs.IsemBridge
import Lax434175.IsemStandard
import Lax888481Proofs.FptMain

/-!
Fixed-parameter tractability of the zoo's `P|M_j|Σ w_j Z_j` under the standard reading,
parameterized by `m + p_max`: the standard word fpt-reduces to the word of interval scheduling
(scale the times, merge the points, pad), where lax-888481's algorithm decides it.
-/

namespace Lax434175Proofs.P200Bridge
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.StandardReading
open Lax434175.ResultParameters Lax434175.IsemLink
open Lax434175Proofs.Points Lax434175Proofs.P200Raw Lax434175Proofs.P200Words
open Lax434175Proofs.P200Bound Lax434175Proofs.P200Programs Lax434175Proofs.P200Param
open Lax888481.Scheduling Lax888481.InstanceEncoding Lax888481.SchedulingProblems
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions

/-- The parameter `m + p_max`. -/
noncomputable abbrev κ : TParameter (problem OperationsFamily.family ZooParallel.p200) :=
  tplus (lift (Ops.m ZooParallel.p200)) (lift (Ops.pmax ZooParallel.p200))

/-- The zoo's problem on its standard words, parameterized by `m + p_max`. -/
noncomputable abbrev Src := parameterized (StandardReading.ops.at ZooParallel.p200) κ

theorem polyTimeOn_restrict {D D' : Set (List ℕ)} {F F' : List ℕ → List ℕ} (h : PolyTimeOn D F)
    (hD : D' ⊆ D) (hF : ∀ x ∈ D', F x = F' x) : PolyTimeOn D' F' := by
  obtain ⟨p, c, d, hc⟩ := h
  exact ⟨p, c, d, fun x hx => by rw [← hF x hx]; exact hc x (hD hx)⟩

/-- The parameter of an instance, read off its data. -/
theorem kappa_eq (x : Inst OperationsFamily.family ZooParallel.p200) (D : ℤ) :
    κ x D = (rawOf x).machines + (if 0 < (rawOf x).machines then Finset.univ.sup (rawOf x).p
      else if 0 < (rawOf x).jobs then 1 else 0) := by
  show x.base.machines + Ops.pmax ZooParallel.p200 x = _
  rw [pmax_eq]
  rfl

/-- The parameter of a word, through the instance the word writes. -/
theorem param_eq {u : List ℕ} {x : Inst OperationsFamily.family ZooParallel.p200} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at ZooParallel.p200) u x D) :
    ∃ (x' : Inst OperationsFamily.family ZooParallel.p200) (D' : ℤ),
      u = stdWordR (rawOf x') D' ∧ Src.param u = κ x' D' := by
  classical
  have hex : ∃ x D, EncodesDecision (StandardReading.ops.at ZooParallel.p200) u x D := ⟨x, D, h⟩
  refine ⟨hex.choose, hex.choose_spec.choose, word_eq _ hex.choose_spec.choose_spec, ?_⟩
  show (if h : ∃ x D, EncodesDecision (StandardReading.ops.at ZooParallel.p200) u x D then
    κ h.choose h.choose_spec.choose else 0) = _
  rw [dif_pos hex]

/-- The answer of a word is the answer of the instance it writes. -/
theorem yes_iff {u : List ℕ} {x : Inst OperationsFamily.family ZooParallel.p200} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at ZooParallel.p200) u x D) :
    Src.Yes u ↔ (rawOf x).Yes D := by
  rw [← Lax434175Proofs.P200Decides.decides_iff]
  constructor
  · rintro ⟨y, D', hy, hd⟩
    obtain ⟨rfl, hi⟩ := Lax434175.Propagation.ops_determined standard_p200 u y x D' D hy h
    exact hi.mp hd
  · exact fun hd => ⟨x, D, h, hd⟩

/-- The empty interval scheduling instance. -/
def empty : Instance where
  jobs := 0
  machines := 0
  p := Fin.elim0
  d := Fin.elim0
  w := Fin.elim0
  eligible := Fin.elim0
  p_pos := fun j => j.elim0
  p_le_d := fun j => j.elim0

theorem encodes_empty : EncodesDecisionInstance [0, 0, 0, 1] empty 1 :=
  ⟨[0, 0, 0], rfl, {
    jobCount_eq := rfl
    machineCount_eq := rfl
    length_eq := rfl
    proc_eq := fun j => j.elim0
    due_eq := fun j => j.elim0
    wt_eq := fun j => j.elim0
    offset_zero := rfl
    offset_mono := fun j hj => absurd hj (by simp [empty])
    target_lt := fun t ht => absurd (show t < 0 from ht) (Nat.not_lt_zero t)
    eligible_iff := fun j => j.elim0 }⟩

theorem not_hasWeight_empty : ¬ empty.HasWeight 1 := by
  rintro ⟨σ, -, hW⟩
  have : empty.weight σ = 0 := by simp [Instance.weight, empty]
  omega

/-- The target's answer on a word that encodes an instance in which every job has a machine. -/
theorem target_yes_iff {w : List ℕ} {I : Instance} {W : ℕ} (h : EncodesDecisionInstance w I W)
    (hI : AllEligible I) : jitByMachinesAndPmax.Yes w ↔ I.HasWeight W := by
  constructor
  · rintro ⟨I', W', h', hd⟩
    obtain ⟨rfl, rfl⟩ := Lax434175Proofs.IsemLink.encodesDecision_unique h h'
    exact (Lax434175Proofs.IsemLink.hasWeight_iff I hI W).mpr hd
  · exact fun hw => ⟨I, W, h, (Lax434175Proofs.IsemLink.hasWeight_iff I hI W).mp hw⟩

theorem allEligible_empty : AllEligible empty := fun j => j.elim0

/-- **The fpt-reduction.** -/
theorem fptReduces : Src ≤ᶠᵖᵗ jitByMachinesAndPmax := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_polyTime (R := toIsemWord) ⟨fun u hu => ?_, fun u hu => ?_⟩
    ⟨g, g_computable, fun u hu => ?_⟩
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_turingPolytime _ toIsemWord_turing)
  · obtain ⟨x, D, h⟩ := hu
    rw [word_eq x h]
    by_cases hR : ∀ j, ((rawOf x).elig j).Nonempty
    · exact ⟨_, _, toIsemWord_spec (rawOf x) D hR, allEligible_pad _⟩
    · rw [toIsemWord_no (rawOf x) D hR]
      exact ⟨empty, 1, encodes_empty, allEligible_empty⟩
  · obtain ⟨x, D, h⟩ := hu
    rw [yes_iff h, word_eq x h]
    by_cases hR : ∀ j, ((rawOf x).elig j).Nonempty
    · rw [target_yes_iff (toIsemWord_spec (rawOf x) D hR) (allEligible_pad _),
        ← Lax434175Proofs.IsemLink.hasWeight_pad, (rawOf x).yes_iff]
      exact ⟨fun h => h.2, fun h => ⟨hR, h⟩⟩
    · rw [toIsemWord_no (rawOf x) D hR, target_yes_iff encodes_empty allEligible_empty]
      exact ⟨fun h => absurd h.1 hR, fun h => absurd h not_hasWeight_empty⟩
  · obtain ⟨x, D, h⟩ := hu
    obtain ⟨x', D', hu, hp⟩ := param_eq h
    rw [hp, hu, kappa_eq]
    show machineCount _ + pmaxOf _ ≤ _
    by_cases hR : ∀ j, ((rawOf x').elig j).Nonempty
    · have he := toIsemWord_spec (rawOf x') D' hR
      rw [machineCount_eq he]
      refine (Nat.add_le_add_left (pmaxOf_le he) _).trans (param_le (rawOf x') hR ?_ ?_)
      · exact Nat.le_add_right _ _
      · intro hm
        rw [if_pos hm]
        exact Nat.le_add_left _ _
    · rw [toIsemWord_no (rawOf x') D' hR]
      exact Nat.zero_le _

/-- The parameter is computed in polynomial time. -/
theorem isParameterized : IsParameterized Src := by
  refine polyTimeOn_restrict ((Lax496464.WH_A5_Bridges.polyTimeOn_univ_iff _).mpr paramWord_polytime)
    (Set.subset_univ _) fun u hu => ?_
  obtain ⟨x, D, h⟩ := hu
  obtain ⟨x', D', hu, hp⟩ := param_eq h
  rw [hp, kappa_eq, hu, paramWord_eq]

-- The target is in FPT

theorem gFpt_computable : Computable Lax888481Proofs.FptMain.gFpt := by
  have hT : Primrec Lax888481Proofs.FptMain.Tof :=
    nat_pow.comp (Primrec.succ) Primrec.id
  have hp : Primrec fun k => (k + 1) ^ Lax888481Proofs.FptMain.Tof k :=
    nat_pow.comp Primrec.succ hT
  have hg : Primrec Lax888481Proofs.FptMain.gFpt :=
    Primrec.nat_mul.comp (Primrec.const 4000)
      (Primrec.nat_mul.comp Primrec.succ (Primrec.nat_mul.comp hT hp))
  exact hg.to_comp

/-- lax-888481's program decides the target. -/
theorem decides_jit : Lax888481.ParameterizedComplexity.Decides jitByMachinesAndPmax
    Lax888481Proofs.FptMain.prog2 12001 Lax888481Proofs.FptMain.gFpt := by
  intro w x hx
  have hdom : x ∈ byMachinesAndPmax.Domain := by
    obtain ⟨I, W, hxI, _⟩ := hx.1
    exact ⟨I, W, hxI⟩
  obtain ⟨t, ht, hrun⟩ := Lax888481Proofs.FptMain.prog2_computesInTime w x ⟨hdom, hx.2⟩
  refine ⟨t, ht, ?_⟩
  beta_reduce at hrun ⊢
  by_cases hy : jitByMachinesAndPmax.Yes x
  · rw [if_pos ((Lax434175Proofs.IsemLink.yes_iff hx.1).mpr hy)] at hrun
    rw [if_pos hy]
    exact hrun
  · rw [if_neg (fun h => hy ((Lax434175Proofs.IsemLink.yes_iff hx.1).mp h))] at hrun
    rw [if_neg hy]
    exact hrun

theorem isParameterized_jit : IsParameterized jitByMachinesAndPmax :=
  polyTimeOn_restrict ((Lax496464.WH_A5_Bridges.polyTimeOn_univ_iff _).mpr isemParam_polytime)
    (Set.subset_univ _) fun x _ => isemParam_eq x

theorem jit_mem_FPT : jitByMachinesAndPmax ∈ FPT :=
  Lax496464.WH_A5_Bridges.mem_FPT_of_decides isParameterized_jit gFpt_computable decides_jit

/--
---
conclusion: Lax434175.IsemStandard.fpt_mPmax
---
The standard word fpt-reduces to the word of interval scheduling, where lax-888481's
algorithm decides the problem in fixed-parameter time.
-/
theorem fpt_mPmax : Lax434175.ZooParallelResults.p200_r1 StandardReading.ops :=
  Lax496464.WH_A3_ReductionCalculus.mem_FPT_of_fptReduces isParameterized fptReduces jit_mem_FPT

end Lax434175Proofs.P200Bridge
