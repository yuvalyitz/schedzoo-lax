import Mathlib.Tactic
import Lax434175.ThresholdWords
import Lax434175Proofs.Thresholds
import Lax434175Proofs.Determined
import Lax434175Proofs.PadReduction
import Lax888481Proofs.TMCompose
import Lax759944.TuringRamPolytimeEquivalence

namespace Lax434175Proofs.ThresholdWords
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results
open Lax434175.ThresholdWords Lax434175.StandardReading Lax434175.ResultParameters

variable {values : (i : OperationsFamily.FieldName) → (OperationsFamily.family.module i).Value}

theorem readThr_thrWord (D : ℤ) : readThr (if D < 0 then 1 else 0) D.natAbs = D := by
  unfold readThr
  by_cases h : D < 0
  · rw [if_pos h, if_neg one_ne_zero]; omega
  · rw [if_neg h, if_pos rfl]; omega

theorem objWord_length {s : Spec OperationsFamily.family} (x : Inst OperationsFamily.family s) :
    (objWord x).length = 3 * x.base.jobs := by
  simp [objWord, objOf, List.length_flatten, List.sum_ofFn, mul_comm]

/-- Rows of three numbers, flattened: position `3 j + k` is number `k` of row `j`. -/
theorem rows_getD : ∀ {n : ℕ} (f : Fin n → List ℕ), (∀ j, (f j).length = 3) →
    ∀ (j : Fin n) (k : ℕ), k < 3 → (List.ofFn f).flatten.getD (3 * j.val + k) 0 = (f j).getD k 0
  | 0, _, _, j, _, _ => j.elim0
  | n + 1, f, hf, j, k, hk => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.val_zero, mul_zero, zero_add]
      rw [List.getD_append _ _ _ _ (by rw [hf]; exact hk)]
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; simp; omega), hf]
      have := rows_getD (fun j => f j.succ) (fun j => hf j.succ) j k hk
      simp only [Fin.val_succ] at this ⊢
      rw [show 3 * (j.val + 1) + k - 3 = 3 * j.val + k by omega]
      exact this

/-- The numbers of the final block. -/
theorem objWord_getD {s : Spec OperationsFamily.family} (x : Inst OperationsFamily.family s)
    (j : Fin x.base.jobs) (k : ℕ) (hk : k < 3) :
    (objWord x).getD (3 * j.val + k) 0 = (objOf x j).getD k 0 :=
  rows_getD (objOf x) (fun _ => rfl) j k hk

open Classical in
/-- The new threshold reads only the first `n` jobs. -/
theorem newThr_congr (mode : StepMode) (n : ℕ) (D : ℤ) {r r' w w' d d' : ℕ → ℕ}
    (hr : ∀ j < n, r j = r' j) (hw : ∀ j < n, w j = w' j) (hd : ∀ j < n, d j = d' j) :
    newThr mode n D r w d = newThr mode n D r' w' d' := by
  cases mode
  · rfl
  · show (if (n = 0 ∧ D < 0) ∨ ∃ j < n, (d j : ℤ) + D < 0 then -1 else 0) =
      (if (n = 0 ∧ D < 0) ∨ ∃ j < n, (d' j : ℤ) + D < 0 then -1 else 0)
    have : (∃ j < n, (d j : ℤ) + D < 0) ↔ ∃ j < n, (d' j : ℤ) + D < 0 :=
      exists_congr fun j => and_congr_right fun hj => by rw [hd j hj]
    simp only [this]
  · rfl
  · show D - ∑ j ∈ Finset.range n, (r j : ℤ) = D - ∑ j ∈ Finset.range n, (r' j : ℤ)
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [hr j (Finset.mem_range.mp hj)]
  · show D - ∑ j ∈ Finset.range n, (w j : ℤ) * (r j : ℤ) =
      D - ∑ j ∈ Finset.range n, (w' j : ℤ) * (r' j : ℤ)
    congr 1
    exact Finset.sum_congr rfl fun j hj => by
      rw [hr j (Finset.mem_range.mp hj), hw j (Finset.mem_range.mp hj)]

/-- A function on the jobs, extended by `0`. -/
def ext {n : ℕ} (f : Fin n → ℕ) (j : ℕ) : ℕ := if h : j < n then f ⟨j, h⟩ else 0

/-- **The map on a standard word**: the prefix stays, the final block and the
threshold are rewritten. -/
theorem stepWord_std (mode : StepMode) {s : Spec OperationsFamily.family}
    (x : Inst OperationsFamily.family s) (P : List ℕ) (hP : 2 ≤ P.length)
    (hn : P.getD 1 0 = x.base.jobs) (D : ℤ) :
    stepWord mode (P ++ objWord x ++ thrWord D) =
      P ++ (List.ofFn fun j : Fin x.base.jobs =>
          [x.base.r j, Ops.weight s x j, newDue mode D (x.base.r j) (Ops.due s x j)]).flatten ++
        thrWord (newThr mode x.base.jobs D (ext x.base.r) (ext (Ops.weight s x))
          (ext (Ops.due s x))) := by
  have hlen := objWord_length x
  have hL : (P ++ objWord x ++ thrWord D).length = P.length + 3 * x.base.jobs + 2 := by
    simp [hlen, thrWord]; omega
  have h1 : (P ++ objWord x ++ thrWord D).getD 1 0 = x.base.jobs := by
    rw [List.append_assoc, List.getD_append _ _ _ _ (by omega), hn]
  have hbase : (P ++ objWord x ++ thrWord D).length - 2 - 3 * x.base.jobs = P.length := by omega
  -- the entries of the word
  have hget : ∀ i, i < 3 * x.base.jobs →
      (P ++ objWord x ++ thrWord D).getD (P.length + i) 0 = (objWord x).getD i 0 := fun i hi => by
    rw [List.getD_append _ _ _ _ (by simp [hlen]; omega), List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hthr1 : (P ++ objWord x ++ thrWord D).getD ((P ++ objWord x ++ thrWord D).length - 2) 0 =
      if D < 0 then 1 else 0 := by
    rw [hL, List.getD_append_right _ _ _ _ (by simp [hlen]; try omega)]
    simp [hlen, thrWord]
  have hthr2 : (P ++ objWord x ++ thrWord D).getD ((P ++ objWord x ++ thrWord D).length - 1) 0 =
      D.natAbs := by
    rw [hL, List.getD_append_right _ _ _ _ (by simp [hlen]; try omega)]
    simp [hlen, thrWord]
  have hrow : ∀ (j : Fin x.base.jobs) (k : ℕ), k < 3 →
      (P ++ objWord x ++ thrWord D).getD (P.length + 3 * j.val + k) 0 = (objOf x j).getD k 0 :=
    fun j k hk => by
      rw [Nat.add_assoc, hget _ (by have := j.isLt; omega), objWord_getD x j k hk]
  unfold stepWord
  rw [if_neg (by rw [hL, h1]; omega)]
  dsimp only
  have htake : (P ++ objWord x ++ thrWord D).take P.length = P := by
    rw [List.append_assoc]; exact List.take_left' rfl
  rw [h1, hbase, hthr1, hthr2, readThr_thrWord, htake]
  congr 2
  · refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
    have e0 := hrow j 0 (by norm_num)
    have e1 := hrow j 1 (by norm_num)
    have e2 := hrow j 2 (by norm_num)
    simp only [add_zero, objOf, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2
    rw [e0, e1, e2]
  · refine newThr_congr mode _ D (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · have := hrow ⟨j, hj⟩ 0 (by norm_num)
      simp only [add_zero, objOf, List.getD_cons_zero] at this
      rw [this, ext, dif_pos hj]
    · have := hrow ⟨j, hj⟩ 1 (by norm_num)
      simp only [objOf, List.getD_cons_succ, List.getD_cons_zero] at this
      rw [this, ext, dif_pos hj]
    · have := hrow ⟨j, hj⟩ 2 (by norm_num)
      simp only [objOf, List.getD_cons_succ, List.getD_cons_zero] at this
      rw [this, ext, dif_pos hj]

-- Correctness on standard words

/-- The specification with an objective. -/
abbrev S (values : (i : OperationsFamily.FieldName) → (OperationsFamily.family.module i).Value)
    (o : Objectives.Value) : Spec OperationsFamily.family := Thresholds.withObjective values o

theorem std_split (hs : values .encoding = .standard) {o : Objectives.Value} {u : List ℕ}
    {x : Inst OperationsFamily.family (S values o)} {D : ℤ}
    (hx : EncodesDecision (ops.at (S values o)) u x D) :
    ∃ P b₁ b₂ b₃, u = P ++ objWord x ++ thrWord D ∧
      P = [0, x.base.jobs, x.base.machines] ++ b₁ ++ b₂ ++ b₃ ∧ Records x b₁ ∧
      Block (pairTuples x) b₂ ∧ Block (globalTuples x) b₃ := by
  obtain ⟨z, rfl, b₂, b₃, hb₂, hb₃, hcase⟩ := hx
  rcases hcase with ⟨-, b₁, hr, rfl⟩ | ⟨hhm, -⟩
  · exact ⟨_, b₁, b₂, b₃, rfl, rfl, hr, hb₂, hb₃⟩
  · exact ForbiddenTimes.Encoding.noConfusion (hs.symm.trans hhm)

/-- The instance with new objective data. -/
def withData {o o' : Objectives.Value} (x : Inst OperationsFamily.family (S values o))
    (od' : OperationsFamily.family.objective.Data o' x.base)
    (oa' : OperationsFamily.family.objective.admits o' x.base od') :
    Inst OperationsFamily.family (S values o') :=
  ⟨x.base, x.data, x.admitted, od', oa'⟩

/-- **Correctness from the new objective data.** -/
theorem correct_of (hs : values .encoding = .standard) {o o' : Objectives.Value}
    (mode : StepMode) {u : List ℕ} {x : Inst OperationsFamily.family (S values o)} {D : ℤ}
    (hx : EncodesDecision (ops.at (S values o)) u x D)
    (od' : OperationsFamily.family.objective.Data o' x.base)
    (oa' : OperationsFamily.family.objective.admits o' x.base od')
    (hw : ∀ j, Ops.weight (S values o') (withData x od' oa') j =
      Ops.weight (S values o) x j)
    (hd : ∀ j, Ops.due (S values o') (withData x od' oa') j =
      newDue mode D (x.base.r j) (Ops.due (S values o) x j))
    (hdec : (problem _ (S values o)).Decides x D ↔
      (problem _ (S values o')).Decides (withData x od' oa')
        (newThr mode x.base.jobs D (ext x.base.r) (ext (Ops.weight (S values o) x))
          (ext (Ops.due (S values o) x)))) :
    ∃ y D', EncodesDecision (ops.at (S values o')) (stepWord mode u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values o)).Decides x D ↔ (problem _ (S values o')).Decides y D') := by
  obtain ⟨P, b₁, b₂, b₃, rfl, hP, hr, hb₂, hb₃⟩ := std_split hs hx
  have hlen : 2 ≤ P.length := by subst hP; simp only [List.length_append, List.length_cons]; omega
  have hn : P.getD 1 0 = x.base.jobs := by subst hP; rfl
  refine ⟨withData x od' oa', _, ?_, rfl, hdec⟩
  refine ⟨P ++ objWord (withData x od' oa'), ?_,
    b₂, b₃, hb₂, hb₃, Or.inl ⟨hs, b₁, hr, by rw [hP]; rfl⟩⟩
  rw [stepWord_std mode x P hlen hn D]
  congr 2
  refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
  exact (congrArg₂ (fun a b => [x.base.r j, a, b]) (hw j) (hd j)).symm

-- The nine steps

open Lax434175.Thresholds in
/-- Jobs complete no earlier than their release dates. -/
theorem releaseRespected : ReleaseRespected values :=
  fun x _ σ _ hf hc j => le_trans (hc .releaseDates j) (Operations.startsBeforeCompletion x σ hf j)

theorem ext_val {n : ℕ} (f : Fin n → ℕ) (j : Fin n) : ext f j.val = f j := by
  unfold ext; exact dif_pos j.isLt

theorem dec_thr {o : Objectives.Value} (y : Inst OperationsFamily.family (S values o)) {t t' : ℤ}
    (e : t = t') :
    (problem _ (S values o)).Decides y t ↔ (problem _ (S values o)).Decides y t' := by
  subst e; rfl

theorem sum_ext {n : ℕ} (f : Fin n → ℕ) :
    ∑ j ∈ Finset.range n, (ext f j : ℤ) = ∑ j, (f j : ℤ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => congrArg (fun a : ℕ => (a : ℤ)) (ext_val f j)

theorem sum_ext₂ {n : ℕ} (f g : Fin n → ℕ) :
    ∑ j ∈ Finset.range n, (ext f j : ℤ) * (ext g j : ℤ) = ∑ j, (f j : ℤ) * (g j : ℤ) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (ext f j : ℤ) * (ext g j : ℤ))]
  exact Finset.sum_congr rfl fun j _ =>
    congrArg₂ (fun a b : ℕ => (a : ℤ) * (b : ℤ)) (ext_val f j) (ext_val g j)

open Classical in
theorem tardy_eq (x : Inst OperationsFamily.family (S values .lmax)) (D : ℤ) (w : ℕ → ℕ) :
    Thresholds.tardyThreshold values x D =
      newThr .lateShift x.base.jobs D (ext x.base.r) w (ext (Ops.due (S values .lmax) x)) := by
  unfold Thresholds.tardyThreshold
  show _ = (if (x.base.jobs = 0 ∧ D < 0) ∨ ∃ j < x.base.jobs,
      ((ext (Ops.due (S values .lmax) x) j : ℕ) : ℤ) + D < 0 then -1 else 0)
  congr 1
  apply propext
  refine or_congr Iff.rfl ⟨fun ⟨j, hj⟩ => ⟨j.val, j.isLt,
      (congrArg (fun a : ℕ => (a : ℤ) + D < 0) (ext_val (Ops.due (S values .lmax) x) j)).mpr hj⟩,
    fun ⟨j, hj, h⟩ => ⟨⟨j, hj⟩,
      (congrArg (fun a : ℕ => (a : ℤ) + D < 0) (ext_val (Ops.due (S values .lmax) x) ⟨j, hj⟩)).mp h⟩⟩

theorem makespan_iff_sumT (x : Inst OperationsFamily.family (S values .makespan)) (D : ℤ) :
    (problem _ (S values .makespan)).Decides x D ↔
      (problem _ (S values .sumT)).Decides
        (withData x (o' := .sumT) (fun _ => D.toNat) trivial) (Thresholds.lateThreshold D) := by
  have key := fun σ => Lax434175Proofs.Thresholds.makespan_iff_zero x.base σ D _
    (Lax434175Proofs.Thresholds.sumT_le_zero x.base σ (fun _ => D.toNat))
    (Lax434175Proofs.Thresholds.sumT_not_le x.base σ _)
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).2 hc⟩

-- Size of the word map

theorem stepWord_length (mode : StepMode) (u : List ℕ) : (stepWord mode u).length = u.length := by
  unfold stepWord
  split_ifs with h
  · rfl
  · simp only [List.length_append, List.length_take, List.length_flatten, List.map_ofFn,
      List.sum_ofFn, thrWord, List.length_cons, List.length_nil, Function.comp_def]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega

theorem maxEntry_le {w : List ℕ} {K : ℕ} (h : ∀ v ∈ w, v ≤ K) : maxEntry w ≤ K := by
  unfold maxEntry
  induction w with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem readThr_natAbs (neg a : ℕ) : (readThr neg a).natAbs = a := by
  unfold readThr; split_ifs <;> omega

theorem readThr_le (neg a : ℕ) : readThr neg a ≤ a ∧ -(a : ℤ) ≤ readThr neg a := by
  unfold readThr; split_ifs <;> omega

theorem newThr_natAbs_le (mode : StepMode) (n : ℕ) (D : ℤ) (r w d : ℕ → ℕ) (M : ℕ)
    (hD : D.natAbs ≤ M) (hr : ∀ j < n, r j ≤ M) (hw : ∀ j < n, w j ≤ M) :
    (newThr mode n D r w d).natAbs ≤ (n + 1) * (M + 1) ^ 2 := by
  have h1 : 1 ≤ (n + 1) * (M + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : M + n * M ≤ (n + 1) * (M + 1) ^ 2 := by nlinarith
  have h3 : M + n * (M * M) ≤ (n + 1) * (M + 1) ^ 2 := by nlinarith
  cases mode with
  | lateConst => simp only [newThr]; split_ifs <;> simp; omega
  | lateShift => simp only [newThr]; split_ifs <;> simp; omega
  | toRelease => simp only [newThr]; omega
  | shift =>
    simp only [newThr]
    have hS0 : 0 ≤ ∑ j ∈ Finset.range n, (r j : ℤ) := Finset.sum_nonneg fun _ _ => by positivity
    have hS : ∑ j ∈ Finset.range n, (r j : ℤ) ≤ (n * M : ℕ) := by
      have := Finset.sum_le_card_nsmul (Finset.range n) (fun j => (r j : ℤ)) (M : ℤ)
        (fun j hj => by exact_mod_cast hr j (Finset.mem_range.mp hj))
      simpa using this
    generalize ∑ j ∈ Finset.range n, (r j : ℤ) = S at hS0 hS
    generalize n * M = K at hS h2
    omega
  | weightedShift =>
    simp only [newThr]
    have hS0 : 0 ≤ ∑ j ∈ Finset.range n, (w j : ℤ) * (r j : ℤ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hS : ∑ j ∈ Finset.range n, (w j : ℤ) * (r j : ℤ) ≤ (n * (M * M) : ℕ) := by
      have := Finset.sum_le_card_nsmul (Finset.range n) (fun j => (w j : ℤ) * (r j : ℤ))
        ((M * M : ℕ) : ℤ) (fun j hj => by
          have := Finset.mem_range.mp hj
          push_cast
          exact mul_le_mul (by exact_mod_cast hw j this) (by exact_mod_cast hr j this)
            (by positivity) (by positivity))
      simpa using this
    generalize ∑ j ∈ Finset.range n, (w j : ℤ) * (r j : ℤ) = S at hS0 hS
    generalize n * (M * M) = K at hS h3
    omega

/-- Every number the word map writes is at most `(|u| + 1) (M + 1)²`, for the
largest number `M` of the word. -/
theorem stepWord_le (mode : StepMode) (u : List ℕ) :
    ∀ v ∈ stepWord mode u, v ≤ (u.length + 1) * (maxEntry u + 1) ^ 2 := by
  set M := maxEntry u
  have hu : ∀ v ∈ u, v ≤ M := fun v hv => Lax434175Proofs.PadWord.le_foldr_max hv
  have hg : ∀ i, u.getD i 0 ≤ M := Lax434175Proofs.PadReduction.getD_le hu
  have hM : M ≤ (u.length + 1) * (M + 1) ^ 2 := by nlinarith
  have h2M : M + M ≤ (u.length + 1) * (M + 1) ^ 2 := by nlinarith
  have h1 : 1 ≤ (u.length + 1) * (M + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  intro v hv
  unfold stepWord at hv
  split_ifs at hv with h
  · exact (hu v hv).trans hM
  · simp only [List.mem_append, List.mem_flatten, List.mem_ofFn, thrWord, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with ((hv | ⟨l, ⟨j, rfl⟩, hv⟩) | (rfl | rfl))
    · exact (hu v (List.mem_of_mem_take hv)).trans hM
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact (hg _).trans hM
      · exact (hg _).trans hM
      · have hd := hg (u.length - 2 - 3 * u.getD 1 0 + 3 * j + 2)
        have ha := hg (u.length - 1)
        have hr := hg (u.length - 2 - 3 * u.getD 1 0 + 3 * j)
        have hneg := readThr_le (u.getD (u.length - 2) 0) (u.getD (u.length - 1) 0)
        cases mode <;> simp only [newDue] <;> omega
    · split_ifs <;> omega
    · refine (newThr_natAbs_le _ _ _ _ _ _ M (by rw [readThr_natAbs]; exact hg _)
        (fun j _ => hg _) (fun j _ => hg _)).trans ?_
      have : u.getD 1 0 ≤ u.length := by omega
      exact Nat.mul_le_mul_right _ (by omega)

variable (hs : values .encoding = .standard) {u : List ℕ} {D : ℤ}
include hs

theorem step_makespan_sumU {x : Inst OperationsFamily.family (S values .makespan)}
    (hx : EncodesDecision (ops.at (S values .makespan)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumU)) (stepWord .lateConst u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .makespan)).Decides x D ↔ (problem _ (S values .sumU)).Decides y D') :=
  correct_of hs .lateConst hx (fun _ => D.toNat) trivial (fun _ => rfl) (fun _ => rfl)
    (Lax434175Proofs.Thresholds.makespan_iff_sumU values x D)

theorem step_makespan_sumT {x : Inst OperationsFamily.family (S values .makespan)}
    (hx : EncodesDecision (ops.at (S values .makespan)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumT)) (stepWord .lateConst u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .makespan)).Decides x D ↔ (problem _ (S values .sumT)).Decides y D') :=
  correct_of hs .lateConst hx (fun _ => D.toNat) trivial (fun _ => rfl) (fun _ => rfl)
    (makespan_iff_sumT x D)

theorem step_lmax_sumU {x : Inst OperationsFamily.family (S values .lmax)}
    (hx : EncodesDecision (ops.at (S values .lmax)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumU)) (stepWord .lateShift u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .lmax)).Decides x D ↔ (problem _ (S values .sumU)).Decides y D') :=
  correct_of hs .lateShift hx (Thresholds.toLateShifted values x D).objectiveData trivial (fun _ => rfl)
    (fun _ => rfl) ((Lax434175Proofs.Thresholds.lmax_iff_sumU values x D).trans (dec_thr _ (tardy_eq x D _)))

theorem step_lmax_sumT {x : Inst OperationsFamily.family (S values .lmax)}
    (hx : EncodesDecision (ops.at (S values .lmax)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumT)) (stepWord .lateShift u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .lmax)).Decides x D ↔ (problem _ (S values .sumT)).Decides y D') :=
  correct_of hs .lateShift hx (Thresholds.toTardy values x D).objectiveData trivial (fun _ => rfl)
    (fun _ => rfl) ((Lax434175Proofs.Thresholds.lmax_iff_sumT values x D).trans (dec_thr _ (tardy_eq x D _)))

theorem step_sumF_sumT {x : Inst OperationsFamily.family (S values .sumF)}
    (hx : EncodesDecision (ops.at (S values .sumF)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumT)) (stepWord .toRelease u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .sumF)).Decides x D ↔ (problem _ (S values .sumT)).Decides y D') :=
  correct_of hs .toRelease hx _ trivial (fun _ => rfl) (fun _ => rfl)
    (Lax434175Proofs.Thresholds.sumF_iff_sumT values x D)

theorem step_sumWF_sumWT {x : Inst OperationsFamily.family (S values .sumWF)}
    (hx : EncodesDecision (ops.at (S values .sumWF)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumWT)) (stepWord .toRelease u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .sumWF)).Decides x D ↔ (problem _ (S values .sumWT)).Decides y D') :=
  correct_of hs .toRelease hx _ trivial (fun _ => rfl) (fun _ => rfl)
    (Lax434175Proofs.Thresholds.sumWF_iff_sumWT values x D)

theorem step_fmax_lmax {x : Inst OperationsFamily.family (S values .fmax)}
    (hx : EncodesDecision (ops.at (S values .fmax)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .lmax)) (stepWord .toRelease u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .fmax)).Decides x D ↔ (problem _ (S values .lmax)).Decides y D') :=
  correct_of hs .toRelease hx (Thresholds.flowToLateness values x).objectiveData trivial
    (fun _ => rfl) (fun _ => rfl) (Lax434175Proofs.Thresholds.fmax_iff_lmax values releaseRespected x D)

theorem step_sumC_sumF {x : Inst OperationsFamily.family (S values .sumC)}
    (hx : EncodesDecision (ops.at (S values .sumC)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumF)) (stepWord .shift u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .sumC)).Decides x D ↔ (problem _ (S values .sumF)).Decides y D') :=
  correct_of hs .shift hx () trivial (fun _ => rfl) (fun _ => rfl)
    ((Lax434175Proofs.Thresholds.sumC_iff_sumF values releaseRespected x D).trans
      (dec_thr _ (congrArg (D - ·) (sum_ext x.base.r)).symm))

theorem step_sumWC_sumWF {x : Inst OperationsFamily.family (S values .sumWC)}
    (hx : EncodesDecision (ops.at (S values .sumWC)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values .sumWF)) (stepWord .weightedShift u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values .sumWC)).Decides x D ↔ (problem _ (S values .sumWF)).Decides y D') :=
  correct_of hs .weightedShift hx (Thresholds.toWeightedFlow values x).objectiveData trivial
    (fun _ => rfl) (fun _ => rfl)
    ((Lax434175Proofs.Thresholds.sumWC_iff_sumWF values releaseRespected x D).trans
      (dec_thr _ (congrArg (D - ·) (sum_ext₂ (Ops.weight (S values .sumWC) x) x.base.r)).symm))

/-- The nine steps, each from the new objective data and the iff of `Thresholds`. -/
theorem stepWord_correct_aux {o o' : Objectives.Value} {mode : StepMode}
    (hm : stepOf o o' = some mode) {x : Inst OperationsFamily.family (S values o)}
    (hx : EncodesDecision (ops.at (S values o)) u x D) :
    ∃ y D', EncodesDecision (ops.at (S values o')) (stepWord mode u) y D' ∧
      y.base = x.base ∧ ((problem _ (S values o)).Decides x D ↔ (problem _ (S values o')).Decides y D') := by
  cases o <;> cases o' <;> simp only [stepOf, Option.some.injEq, reduceCtorEq] at hm <;>
    subst hm <;>
    first
    | exact step_makespan_sumU hs hx | exact step_makespan_sumT hs hx
    | exact step_lmax_sumU hs hx | exact step_lmax_sumT hs hx
    | exact step_sumF_sumT hs hx | exact step_sumWF_sumWT hs hx
    | exact step_fmax_lmax hs hx | exact step_sumC_sumF hs hx
    | exact step_sumWC_sumWF hs hx

omit hs in
/--
---
conclusion: Lax434175.ThresholdWords.stepWord_correct
---
The nine steps, each from the new objective data and the iff of `Thresholds`.
-/
theorem stepWord_correct (hs : values .encoding = .standard) {o o' : Objectives.Value}
    {mode : StepMode} (hm : stepOf o o' = some mode) {u : List ℕ}
    {x : Inst OperationsFamily.family (Thresholds.withObjective values o)} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at (Thresholds.withObjective values o)) u x D) :
    ∃ y D', EncodesDecision (StandardReading.ops.at (Thresholds.withObjective values o'))
        (stepWord mode u) y D' ∧
      ((problem _ (Thresholds.withObjective values o)).Decides x D ↔
        (problem _ (Thresholds.withObjective values o')).Decides y D') := by
  obtain ⟨y, D', hy, -, hdec⟩ := stepWord_correct_aux hs hm hx
  exact ⟨y, D', hy, hdec⟩

omit hs in
/-- The step keeps the kernel instance: the stepped word encodes an instance with the same
jobs, machines, processing times and release dates. -/
theorem stepWord_correct_base (hs : values .encoding = .standard) {o o' : Objectives.Value}
    {mode : StepMode} (hm : stepOf o o' = some mode) {u : List ℕ}
    {x : Inst OperationsFamily.family (Thresholds.withObjective values o)} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at (Thresholds.withObjective values o)) u x D) :
    ∃ y D', EncodesDecision (StandardReading.ops.at (Thresholds.withObjective values o'))
        (stepWord mode u) y D' ∧ y.base = x.base ∧
      ((problem _ (Thresholds.withObjective values o)).Decides x D ↔
        (problem _ (Thresholds.withObjective values o')).Decides y D') :=
  stepWord_correct_aux hs hm hx

-- Hardness along the steps

theorem yes_iff_of {o : Objectives.Value} {u : List ℕ}
    {x : Inst OperationsFamily.family (S values o)} {D : ℤ}
    (hx : EncodesDecision (ops.at (S values o)) u x D) :
    (decision (ops.at (S values o))).Yes u ↔ (problem _ (S values o)).Decides x D := by
  constructor
  · rintro ⟨x', D', hx', h⟩
    obtain ⟨-, hi⟩ := Lax434175.Propagation.ops_determined (t := S values o) hs u x' x D' D hx' hx
    exact hi.mp h
  · exact fun h => ⟨x, D, hx, h⟩

theorem step_yes {o o' : Objectives.Value} {mode : StepMode} (hm : stepOf o o' = some mode)
    {u : List ℕ} (hu : u ∈ (decision (ops.at (S values o))).Domain) :
    stepWord mode u ∈ (decision (ops.at (S values o'))).Domain ∧
      ((decision (ops.at (S values o))).Yes u ↔
        (decision (ops.at (S values o'))).Yes (stepWord mode u)) := by
  obtain ⟨x, D, hx⟩ := hu
  obtain ⟨y, D', hy, -, hdec⟩ := stepWord_correct_aux hs hm hx
  exact ⟨⟨y, D', hy⟩, (yes_iff_of hs hx).trans (hdec.trans (yes_iff_of hs hy).symm)⟩

/--
---
conclusion: Lax434175.ThresholdWords.npHard_step
---
Compose the reduction with the word map.
-/
theorem npHard_step {o o' : Objectives.Value} {mode : StepMode} (hm : stepOf o o' = some mode) :
    NPHard (ops.at (S values o)) → NPHard (ops.at (S values o')) := by
  intro H A hA
  obtain ⟨f, ⟨t1⟩, hf⟩ := H A hA
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    (stepWord_polytime mode)
  obtain ⟨t⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  refine ⟨_, ⟨t⟩, fun a => ?_⟩
  obtain ⟨hd, hiff⟩ := hf a
  obtain ⟨hd', hy⟩ := step_yes hs hm hd
  exact ⟨hd', hiff.trans hy⟩

/--
---
conclusion: Lax434175.ThresholdWords.stronglyNPHard_step
---
Compose the reduction with the word map; its numbers grow at most polynomially.
-/
theorem stronglyNPHard_step {o o' : Objectives.Value} {mode : StepMode}
    (hm : stepOf o o' = some mode) :
    StronglyNPHard (ops.at (S values o)) → StronglyNPHard (ops.at (S values o')) := by
  rintro ⟨c, d, H⟩
  refine ⟨(c + 1) ^ 2, 2 * d + 1, fun A hA => ?_⟩
  obtain ⟨f, ⟨t1⟩, hf⟩ := H A hA
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    (stepWord_polytime mode)
  obtain ⟨t⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  refine ⟨_, ⟨t⟩, fun a => ?_⟩
  obtain ⟨⟨hd, hsmall⟩, hiff⟩ := hf a
  obtain ⟨hd', hy⟩ := step_yes hs hm hd
  refine ⟨⟨hd', fun v hv => ?_⟩, hiff.trans hy⟩
  simp only [Function.comp_apply, stepWord_length] at hv ⊢
  set L := (f a).length
  have hM : maxEntry (f a) + 1 ≤ (c + 1) * (L + 1) ^ d := by
    have := maxEntry_le hsmall
    have : 1 ≤ (L + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc v ≤ (L + 1) * (maxEntry (f a) + 1) ^ 2 := stepWord_le mode _ v hv
    _ ≤ (L + 1) * ((c + 1) * (L + 1) ^ d) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 2)
    _ = (c + 1) ^ 2 * (L + 1) ^ (2 * d + 1) := by ring

end Lax434175Proofs.ThresholdWords
