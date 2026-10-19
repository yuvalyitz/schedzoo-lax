import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import Lax434175Proofs.JitTimesFacts
import Lax434175Proofs.RamCompose.Programs
import Lax434175.JitFlowShopTimes

/-!
The running times of the zoo's `FF(1,m)||Σw_jZ_j` (`p316`) from Theorems 2 and 3 of
lax-496464. The program is the composition of three: the gathering program reads the numbers it
needs by their positions (`JitTimesGather`), the word map writes the word of lax-496464 with the
same answer (`JitTimesMap`), and the program of lax-496464 decides it. One theorem
(`decidesWithinWide_of`) does the composition for any of the three programs of lax-496464, given
a bound on its main term by the running time.
-/

namespace Lax434175Proofs.JitTimes
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.StandardReading
open Lax434175.ResultParameters Lax434175.JitFlowShop
open Lax496464.FlowShop Lax496464.WordEncoding Lax496464.Problems Lax496464.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax808846Proofs.Simulation
open Lax434175Proofs.JitTimesWords Lax434175Proofs.JitTimesSem Lax434175Proofs.JitTimesTape
open Lax434175Proofs.JitTimesGather Lax434175Proofs.JitTimesFacts
open Lax434175Proofs.RamCompose.Programs Lax434175Proofs.RamCompose.Translate

/-- The standard reading of `p316` on the instances whose last operations have positive length. -/
noncomputable abbrev Rr : PReading ((problem OperationsFamily.family ZooShops.p316).restrict
    (Ops.lastPositive ZooShops.p316)) :=
  (StandardReading.ops.at ZooShops.p316).restrict (Ops.lastPositive ZooShops.p316)

/-! ### Arithmetic -/

theorem log_le_self (n : ℕ) : Nat.log 2 n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    have h2 : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
    omega

theorem log_four (n : ℕ) (hn : 0 < n) : Nat.log 2 (4 * n + 5) ≤ Nat.log 2 n + 4 := by
  have h : 4 * n + 5 ≤ n * 2 * 2 * 2 * 2 := by omega
  refine (Nat.log_mono_right h).trans (le_of_eq ?_)
  rw [Nat.log_mul_base (by norm_num) (by positivity), Nat.log_mul_base (by norm_num) (by positivity),
    Nat.log_mul_base (by norm_num) (by positivity), Nat.log_mul_base (by norm_num) (by omega)]

/-- The sorting term of a word of at most `4 n + 3` numbers. -/
theorem sortCost_le {y : List ℕ} {n : ℕ} (hy : y.length ≤ 4 * n + 3) :
    sortCost y ≤ 40 * (n * Nat.log 2 n + n + 1) := by
  unfold sortCost
  have h1 : (y.length + 1) * (Nat.log 2 (y.length + 2) + 1) ≤ (4 * n + 4) * (Nat.log 2 (4 * n + 5) + 1) :=
    Nat.mul_le_mul (by omega) (by have := Nat.log_mono_right (b := 2) (show y.length + 2 ≤ 4 * n + 5 by omega); omega)
  refine h1.trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Nat.log 2 5 = 2 := by norm_num [Nat.log]
    simp [this]
  · have h2 := log_four n hn
    have h3 := log_le_self n
    have h4 : (4 * n + 4) * (Nat.log 2 (4 * n + 5) + 1) ≤ (4 * n + 4) * (Nat.log 2 n + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    refine h4.trans ?_
    have e : (4 * n + 4) * (Nat.log 2 n + 5) = 4 * (n * Nat.log 2 n) + 20 * n + 4 * Nat.log 2 n + 20 := by ring
    rw [e]; omega

/-- `(n + 1)^k ≤ 3 n^k` for `k ≤ n`. -/
theorem succ_pow_le {n k : ℕ} (hk : k ≤ n) (hn : 0 < n) : (n + 1) ^ k ≤ 3 * n ^ k := by
  have hr : ((n + 1 : ℕ) : ℝ) ^ k ≤ 3 * (n : ℝ) ^ k := by
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have e : ((n + 1 : ℕ) : ℝ) = n * (1 + 1 / n) := by push_cast; field_simp
    rw [e, mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : (1 + 1 / (n : ℝ)) ^ k ≤ Real.exp (k / n) := by
      calc (1 + 1 / (n : ℝ)) ^ k ≤ (Real.exp (1 / n)) ^ k :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (n : ℝ))]) k
        _ = Real.exp (k / n) := by rw [← Real.exp_nat_mul]; ring_nf
    have h2 : Real.exp (k / n) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by rw [div_le_one hnr]; exact_mod_cast hk)
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  exact_mod_cast hr

theorem n_le_log (n : ℕ) : n ≤ n * Nat.log 2 n + 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · omega
  · have : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using h)
    nlinarith

theorem entry_le_maxEntry {u : List ℕ} {v : ℕ} (h : v ∈ u) : v ≤ maxEntry u :=
  Lax434175Proofs.PadWord.le_foldr_max h

/-- The word of lax-496464 is a small one or the word of the instance. -/
theorem theirWord_cases (J : Instance) (D : ℤ) :
    (∃ b ≤ 1, theirWord J D = [0, 0, b]) ∨
      (0 < J.jobs ∧ 0 < J.machines ∧ 0 ≤ D ∧ D < totalWeight J ∧
        theirWord J D = bigWord J ((totalWeight J : ℤ) - D).toNat) := by
  unfold theirWord
  by_cases h0 : J.jobs = 0
  · rw [if_pos h0]; left; exact ⟨_, by split_ifs <;> omega, rfl⟩
  rw [if_neg h0]
  by_cases h1 : J.machines = 0 ∨ D < 0
  · rw [if_pos h1]; left; exact ⟨1, le_rfl, rfl⟩
  rw [if_neg h1]
  by_cases h2 : (totalWeight J : ℤ) ≤ D
  · rw [if_pos h2]; left; exact ⟨0, by omega, rfl⟩
  rw [if_neg h2]; right; exact ⟨by omega, by omega, by omega, by omega, rfl⟩

/-! ### The composition -/

open Classical in
/-- **The composition**, for any of the programs of lax-496464 whose main term `G` is bounded by
the running time `T` on the words the word map writes. -/
theorem decidesWithinWide_of {prog : Program} {c' A : ℕ} {G : List ℕ → ℕ}
    (hprog : ∀ w, ComputesInTime w prog
      {y | y ∈ DecisionInstances ∧ Fits c' w y ∧ c' * G y ≤ 2 ^ w ∧
        (∀ j < jobCount y, 0 < procTime y j)}
      (fun y => if Yes y then [1] else [0]) (fun y => c' * G y + c' * sortCost y))
    (T : ((problem OperationsFamily.family ZooShops.p316).restrict
      (Ops.lastPositive ZooShops.p316)).Inst → ℕ)
    (hsmall : ∀ b ≤ 1, G [0, 0, b] ≤ A)
    (hbig : ∀ x W, 1 ≤ W → W ≤ totalWeight (jOf x.1) → 0 < (jOf x.1).jobs →
      0 < (jOf x.1).machines → G (bigWord (jOf x.1) W) ≤ A * (T x + 1))
    (hlog : ∀ x, (jOf x.1).jobs * Nat.log 2 (jOf x.1).jobs ≤ T x) :
    DecidesWithinWide Rr T := by
  set pc := compileProgram Lax434175Proofs.JitTimesMap.layout Lax434175Proofs.JitTimesMap.com
    with hpc
  set LT := lits gather + lits pc + lits (strip prog) + lits (compose pc (strip prog)) + lits prog
    with hLT
  set C := 3004000 + 1000 * c' * (A + 80) + 64 * c' * (A + 1) + 1000 * c' + 1000 + 4 * LT with hC
  refine ⟨compose gather (compose pc (strip prog)), C, fun u x D hx ℓ hℓ hT => ?_⟩
  have hC3 : 3004000 + 1000 * c' * (A + 80) + 64 * c' * (A + 1) + 1000 * c' + 997 + 4 * LT ≤ C - 3 := by
    omega
  clear_value C
  have hu : u = stdWord (jOf x.1) D := word_eq x.1 hx
  subst hu
  set J := jOf x.1 with hJ
  set n := J.jobs with hn
  set Z := Zb J D with hZ
  set Q := Z + 2 with hQ
  -- the word length
  have hQC : Q ^ C ≤ 2 ^ ℓ := hℓ
  have hCl : C ≤ ℓ :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp ((Nat.pow_le_pow_left (by omega : 2 ≤ Q) C).trans hQC)
  obtain ⟨w, rfl⟩ : ∃ w, ℓ = w + 6 := ⟨ℓ - 6, by omega⟩
  have hK : (C - 3) * Q ^ 4 ≤ 64 * 2 ^ w := by
    have h1 : C - 3 ≤ 2 ^ (C - 4) := by
      have := Nat.lt_two_pow_self (n := C - 4); omega
    have h2 : 2 ^ (C - 4) ≤ Q ^ (C - 4) := Nat.pow_le_pow_left (by omega) _
    have h3 : Q ^ (C - 4) * Q ^ 4 = Q ^ C := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have h4 : 2 ^ (w + 6) = 64 * 2 ^ w := by rw [pow_add]; ring
    calc (C - 3) * Q ^ 4 ≤ Q ^ (C - 4) * Q ^ 4 := Nat.mul_le_mul_right _ (h1.trans h2)
      _ = Q ^ C := h3
      _ ≤ 2 ^ (w + 6) := hQC
      _ = 64 * 2 ^ w := h4
  have hQ1 : Q ≤ Q ^ 4 := Nat.le_self_pow (by norm_num) _
  have hQ2 : Q * Q ≤ Q ^ 4 := by
    calc Q * Q = Q ^ 2 := by ring
      _ ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hQ3 : Q * Q * Q ≤ Q ^ 4 := by
    calc Q * Q * Q = Q ^ 3 := by ring
      _ ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hQ16 : 16 ≤ Q ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ Q ^ 4 := Nat.pow_le_pow_left (by omega) 4
  set P4 := Q ^ 4 with hP4
  have hw4 : 4 * LT + 997 ≤ 4 * 2 ^ w := by
    have : (C - 3) * 16 ≤ (C - 3) * P4 := Nat.mul_le_mul_left _ hQ16
    omega
  have hw2 : 2 ≤ w := by
    by_contra h
    have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpw : ∀ k, 2 ^ w ≤ 2 ^ (w + k) := fun k => Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : 2 ^ (w + 2) = 4 * 2 ^ w := by rw [pow_add]; ring
  have e4 : 2 ^ (w + 4) = 16 * 2 ^ w := by rw [pow_add]; ring
  have e6 : 2 ^ (w + 6) = 64 * 2 ^ w := by rw [pow_add]; ring
  -- a polynomial bound on the numbers
  have hKc : ∀ k, k ≤ C - 3 → k * P4 ≤ 64 * 2 ^ w := fun k hk =>
    (Nat.mul_le_mul_right _ hk).trans hK
  have hnZ : n ≤ Z := jobs_le J D
  have hMZ : J.machines + 1 ≤ Z := machines_le J D
  have hK3 := hKc 3004000 (by omega)
  have huZ : (stdWord J D).length ≤ Z := by simp only [hZ, Zb]; omega
  have hmZ : maxEntry (stdWord J D) ≤ Z := by simp only [hZ, Zb]; omega
  -- the gathering program
  have hgB : 20 + (tape (stdWord J D)).length +
      ((tape (stdWord J D)).getD 2 0 + 1) * stride ((tape (stdWord J D)).getD 3 0) +
      3 * (tape (stdWord J D)).getD 2 0 < 2 ^ (w + 4) := by
    rw [getD_two, getD_three]
    have h1 : (J.jobs + 1) * stride (J.machines + 1) ≤ Q * (28 * Q) :=
      Nat.mul_le_mul (by omega) (by unfold stride; omega)
    have h2 : Q * (28 * Q) = 28 * (Q * Q) := by ring
    simp only [tape, List.length_cons]
    omega
  have hgX : ∀ v ∈ tape (stdWord J D), v < 2 ^ (w + 4) := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := entry_le_maxEntry hv; omega
  have hg := gather_runsTo hgB hgX
  rw [gatherOut_tape, getD_two] at hg
  -- the word map
  obtain ⟨ext, σ', hrun, hout⟩ := Lax434175Proofs.JitTimesMap.run_com J D
  obtain ⟨k, hk, hbs⟩ := hrun
  have hcl : (compact J D).length = 4 * n + 4 := Lax434175Proofs.JitTimesMap.length_compact J D
  have hcm : maxEntry (compact J D) ≤ Z := maxEntry_compact J D
  set Bc := Lax434175Proofs.JitTimesMap.bnd (compact J D) with hBc
  set a := (compact J D).length + maxEntry (compact J D) + 2 with ha
  have haQ : a ≤ 5 * Q := by omega
  have ha3 : a ≤ a ^ 3 := Nat.le_self_pow (by norm_num) _
  have hBca : Bc = 4 * a ^ 3 := rfl
  have hBcQ : Bc ≤ 500 * (Q * Q * Q) := by
    have : a ^ 3 ≤ (5 * Q) ^ 3 := Nat.pow_le_pow_left haQ 3
    have e : (5 * Q) ^ 3 = 125 * (Q * Q * Q) := by ring
    omega
  have hfit : Lax434175Proofs.JitTimesMap.layout.FitsWords Bc (w + 2) := by
    refine fitsWords_of_max_le (by omega) ?_
    simp only [Layout.span, Lax434175Proofs.JitTimesMap.layout, List.length_cons, List.length_nil]
    omega
  have hxin : ∀ v ∈ (compact J D).length :: compact J D, v < Bc := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := entry_le_maxEntry hv; omega
  obtain ⟨t2, ht2, hr2⟩ := compileProgram_runsTo hfit Lax434175Proofs.JitTimesMap.com_ok hxin hbs
  rw [hout, ← hpc] at hr2
  -- the program of lax-496464
  set y' := theirWord J D with hy'
  have hyl : y'.length ≤ 4 * n + 3 := length_theirWord J D
  have hyv : ∀ v ∈ y', v ≤ 4 * (Z + 1) ^ 3 := theirWord_le J D
  have hZ13 : (Z + 1) ^ 3 ≤ Q * Q * Q := by
    have : (Z + 1) ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e : Q ^ 3 = Q * Q * Q := by ring
    omega
  have hq : ∀ j, 0 < J.q j := (lastPositive_iff x.1).mp x.2
  have hcases := theirWord_cases J D
  rw [← hy'] at hcases
  have hGT : G y' ≤ A * (T x + 1) := by
    rcases hcases with ⟨b, hb, e⟩ | ⟨h0, h1, hD0, hD1, e⟩
    · rw [e]; exact (hsmall b hb).trans (Nat.le_mul_of_pos_right _ (by omega))
    · rw [e]; exact hbig x ((totalWeight J : ℤ) - D).toNat (by omega) (by rw [← hJ]; omega) h0 h1
  have hcG : c' * G y' ≤ c' * A * (T x + 1) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ hGT
  have hCT : (64 * c' * (A + 1)) * (T x + 1) ≤ C * (T x + 1) := Nat.mul_le_mul_right _ (by omega)
  have hcA : 64 * (c' * A * (T x + 1)) ≤ (64 * c' * (A + 1)) * (T x + 1) := by
    have : c' * A * (T x + 1) ≤ c' * (A + 1) * (T x + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    calc 64 * (c' * A * (T x + 1)) ≤ 64 * (c' * (A + 1) * (T x + 1)) := by omega
      _ = (64 * c' * (A + 1)) * (T x + 1) := by ring
  have hmem : y' ∈ {y | y ∈ DecisionInstances ∧ Fits c' w y ∧ c' * G y ≤ 2 ^ w ∧
      (∀ j < jobCount y, 0 < procTime y j)} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hcases with ⟨b, hb, e⟩ | ⟨-, -, -, -, e⟩
      · rw [e]; exact mem_decisionInstances emptyI b
      · rw [e]; exact mem_decisionInstances _ _
    · intro v hv
      have h1 := hyv v hv
      have h2 : c' * (y'.length + v + 1) ≤ c' * (9 * P4) := Nat.mul_le_mul_left _ (by omega)
      have h3 := hKc (576 * c') (by omega)
      have e : c' * (9 * P4) * 64 = 576 * c' * P4 := by ring
      generalize c' * (9 * P4) = X at h2 e
      generalize 576 * c' * P4 = Y at h3 e
      generalize 2 ^ w = V at h3 ⊢
      omega
    · have h1 : 64 * (c' * G y') ≤ 64 * 2 ^ w := by
        calc 64 * (c' * G y') ≤ 64 * (c' * A * (T x + 1)) := Nat.mul_le_mul_left _ hcG
          _ ≤ (64 * c' * (A + 1)) * (T x + 1) := hcA
          _ ≤ C * (T x + 1) := hCT
          _ ≤ 2 ^ (w + 6) := hT
          _ = 64 * 2 ^ w := e6
      exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
    · rcases hcases with ⟨b, hb, e⟩ | ⟨-, -, -, -, e⟩
      · rw [e]; intro j hj; simp [jobCount] at hj
      · rw [e]; exact procTime_pos J _ hq
  obtain ⟨t3, ht3, hr3⟩ := hprog w y' hmem
  -- the composition
  obtain ⟨t4, ht4, hr4⟩ := strip_runsTo hw2 (by omega) (by rw [e2]; omega) hr3
  have hLT' : lits gather + lits pc + lits (strip prog) + lits (compose pc (strip prog)) + lits prog = LT :=
    hLT.symm
  have hX5 : ((compact J D).length :: compact J D).length < 2 ^ (w + 2 + 2) := by
    rw [List.length_cons, hcl, show w + 2 + 2 = w + 4 by ring, e4]; omega
  have hX6 : (tape (stdWord J D)).length < 2 ^ (w + 4 + 2) := by
    rw [show w + 4 + 2 = w + 6 by ring, e6]; simp only [tape, List.length_cons]; omega
  obtain ⟨t5, ht5, hr5⟩ := compose_runsTo (v := w + 2) (by omega) (by rw [e2]; omega) (by rw [e2]; omega)
    hX5 (by rw [e2]; omega) hr2 hr4
  obtain ⟨t6, ht6, hr6⟩ := compose_runsTo (v := w + 4) (by omega) (by rw [e4]; omega) (by rw [e4]; omega)
    hX6 (by rw [e4]; omega) hg hr5
  -- the answer
  have hans : (if Yes y' then [1] else [0]) = verdict x D := by
    unfold verdict
    have : Yes y' ↔ ((problem OperationsFamily.family ZooShops.p316).restrict
        (Ops.lastPositive ZooShops.p316)).Decides x D :=
      (yes_theirWord J D).trans (decides_iff x.1 D).symm
    by_cases h : Yes y'
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]
  beta_reduce at hr6
  rw [hans] at hr6
  refine ⟨t6, ?_, hr6⟩
  -- the time
  have hS := sortCost_le hyl
  have hl : n * Nat.log 2 n ≤ T x := hlog x
  have hnl := n_le_log n
  have hcS : c' * sortCost y' ≤ 80 * (c' * (T x + 1)) := by
    have : sortCost y' ≤ 80 * (T x + 1) := by omega
    calc c' * sortCost y' ≤ c' * (80 * (T x + 1)) := Nat.mul_le_mul_left _ this
      _ = 80 * (c' * (T x + 1)) := by ring
  have hkc : k ≤ 300 * (4 * n + 5) := by
    have := hk; simp only [Lax434175Proofs.JitTimesMap.cost, hcl] at this; omega
  have hconst : Lax434175Proofs.JitTimesMap.layout.const = 10 := rfl
  rw [hconst] at ht2
  beta_reduce at ht3
  have hCT2 : (3004000 + 1000 * c' * (A + 80)) * (T x + 1) ≤ C * (T x + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have e7 : (3004000 + 1000 * c' * (A + 80)) * (T x + 1) =
      3004000 * (T x + 1) + 1000 * (c' * A * (T x + 1)) + 80000 * (c' * (T x + 1)) := by ring
  omega

/-! ### The three running times -/

section Small
variable (b : ℕ)

theorem threshold_small : threshold [0, 0, b] = b := rfl
theorem jobCount_small : jobCount [0, 0, b] = 0 := rfl
theorem machineCount_small : machineCount [0, 0, b] = 0 := rfl
theorem qmaxOf_small : qmaxOf [0, 0, b] = 0 := rfl
theorem widthOf_small : widthOf [0, 0, b] = 0 := rfl

end Small

theorem pow_le_pow_both {a b e f : ℕ} (hab : a ≤ b) (hef : e ≤ f) (hb : 1 ≤ b) : a ^ e ≤ b ^ f :=
  (Nat.pow_le_pow_left hab e).trans (Nat.pow_le_pow_right hb hef)

theorem two_mul_W {W S : ℕ} (h1 : 1 ≤ W) (h2 : W ≤ S) : W + 1 ≤ 2 * S := by omega

/--
---
conclusion: Lax434175.JitFlowShopTimes.p316_r1_holds
---
The program of Theorem 2 of lax-496464 after the word map: its main term
`(W - D + 1) (n + 1)^min(m-1, n)` is at most `6 W n^m`.
-/
theorem p316_r1_holds : ZooShopsResults.p316_r1 StandardReading.ops := by
  obtain ⟨prog, c', h⟩ := Lax496464.Theorem2.theorem2_time
  simp only [mul_assoc] at h
  refine decidesWithinWide_of (A := 6)
    (G := fun y => (threshold y + 1) * (jobCount y + 1) ^ machineCount y) h _
    (fun b hb => by simp only [threshold_small, jobCount_small, machineCount_small]; omega)
    (fun x W h1 h2 h0 hm => ?_) (fun x => Nat.le_add_left _ _)
  set J := jOf x.1 with hJ
  simp only [threshold_big, jobCount_big, machineCount_big]
  have hn : Ops.n ZooShops.p316 x.1 = J.jobs := n_eq x.1
  have hm' : Ops.m ZooShops.p316 x.1 = J.machines + 1 := m_eq x.1
  have hW : Ops.totalW ZooShops.p316 x.1 = totalWeight J := totalW_eq x.1
  rw [hn, hm', hW]
  have e1 := two_mul_W h1 h2
  have e2 : (J.jobs + 1) ^ min J.machines J.jobs ≤ 3 * J.jobs ^ min J.machines J.jobs :=
    succ_pow_le (min_le_right _ _) h0
  have e3 : J.jobs ^ min J.machines J.jobs ≤ J.jobs ^ (J.machines + 1) :=
    Nat.pow_le_pow_right h0 (by have := min_le_left J.machines J.jobs; omega)
  calc (W + 1) * (J.jobs + 1) ^ min J.machines J.jobs
      ≤ (2 * totalWeight J) * (3 * J.jobs ^ (J.machines + 1)) :=
        Nat.mul_le_mul e1 (e2.trans (Nat.mul_le_mul_left _ e3))
    _ = 6 * (totalWeight J * J.jobs ^ (J.machines + 1)) := by ring
    _ ≤ 6 * (totalWeight J * J.jobs ^ (J.machines + 1) + J.jobs * Nat.log 2 J.jobs + 1) := by omega

/--
---
conclusion: Lax434175.JitFlowShopTimes.p316_r2_holds
---
The profile sweep of Theorem 3 of lax-496464 after the word map: the word has at most `m - 1`
second-stage machines and the same largest processing time, so its main term is at most
`4 W m^q_max n`.
-/
theorem p316_r2_holds : ZooShopsResults.p316_r2 StandardReading.ops := by
  obtain ⟨prog, c', h⟩ := Lax496464.Theorem3.theorem3_qmax_time
  simp only [mul_assoc] at h
  refine decidesWithinWide_of (A := 4)
    (G := fun y => (threshold y + 1) * ((machineCount y + 1) ^ qmaxOf y * (jobCount y + 1))) h _
    (fun b hb => by
      simp only [threshold_small, jobCount_small, machineCount_small, qmaxOf_small]; omega)
    (fun x W h1 h2 h0 hm => ?_) (fun x => Nat.le_add_left _ _)
  set J := jOf x.1 with hJ
  simp only [threshold_big, jobCount_big, machineCount_big]
  have hn : Ops.n ZooShops.p316 x.1 = J.jobs := n_eq x.1
  have hm' : Ops.m ZooShops.p316 x.1 = J.machines + 1 := m_eq x.1
  have hW : Ops.totalW ZooShops.p316 x.1 = totalWeight J := totalW_eq x.1
  have hq : Ops.qmax ZooShops.p316 x.1 = Finset.univ.sup J.q := qmax_eq x.1
  rw [hn, hm', hW, hq]
  have e1 := two_mul_W h1 h2
  have e2 : (min J.machines J.jobs + 1) ^ qmaxOf (bigWord J W) ≤
      (J.machines + 1) ^ Finset.univ.sup J.q :=
    pow_le_pow_both (by have := min_le_left J.machines J.jobs; omega) (qmaxOf_big J W) (by omega)
  calc (W + 1) * ((min J.machines J.jobs + 1) ^ qmaxOf (bigWord J W) * (J.jobs + 1))
      ≤ (2 * totalWeight J) * ((J.machines + 1) ^ Finset.univ.sup J.q * (2 * J.jobs)) :=
        Nat.mul_le_mul e1 (Nat.mul_le_mul e2 (by omega))
    _ = 4 * (totalWeight J * (J.machines + 1) ^ Finset.univ.sup J.q * J.jobs) := by ring
    _ ≤ 4 * (totalWeight J * (J.machines + 1) ^ Finset.univ.sup J.q * J.jobs +
          J.jobs * Nat.log 2 J.jobs + 1) := by omega

/--
---
conclusion: Lax434175.JitFlowShopTimes.p316_r3_holds
---
The endpoint sweep of Theorem 3 of lax-496464 after the word map: the moved jobs overlap no other
job, so the width of the word is at most `χ + 1` and its main term at most `8 W 2^χ n`.
-/
theorem p316_r3_holds : ZooShopsResults.p316_r3 StandardReading.ops := by
  obtain ⟨prog, c', h⟩ := Lax496464.Theorem3.theorem3_width_time
  simp only [mul_assoc] at h
  refine decidesWithinWide_of (A := 8)
    (G := fun y => (threshold y + 1) * (2 ^ widthOf y * (jobCount y + 1))) h _
    (fun b hb => by
      simp only [threshold_small, jobCount_small, widthOf_small]; omega)
    (fun x W h1 h2 h0 hm => ?_) (fun x => Nat.le_add_left _ _)
  set J := jOf x.1 with hJ
  simp only [threshold_big, jobCount_big]
  have hn : Ops.n ZooShops.p316 x.1 = J.jobs := n_eq x.1
  have hW : Ops.totalW ZooShops.p316 x.1 = totalWeight J := totalW_eq x.1
  have hc : Ops.chi ZooShops.p316 x.1 = overlapJ J := chi_eq x.1
  rw [hn, hW, hc]
  have e1 := two_mul_W h1 h2
  have e2 : 2 ^ widthOf (bigWord J W) ≤ 2 * 2 ^ overlapJ J := by
    have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (widthOf_big J W)
    rw [pow_succ] at this; omega
  calc (W + 1) * (2 ^ widthOf (bigWord J W) * (J.jobs + 1))
      ≤ (2 * totalWeight J) * ((2 * 2 ^ overlapJ J) * (2 * J.jobs)) :=
        Nat.mul_le_mul e1 (Nat.mul_le_mul e2 (by omega))
    _ = 8 * (totalWeight J * 2 ^ overlapJ J * J.jobs) := by ring
    _ ≤ 8 * (totalWeight J * 2 ^ overlapJ J * J.jobs + J.jobs * Nat.log 2 J.jobs + 1) := by omega

end Lax434175Proofs.JitTimes
