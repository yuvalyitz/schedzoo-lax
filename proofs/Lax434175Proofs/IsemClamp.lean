import Mathlib.Tactic
import Lax434175Proofs.IsemPrograms

/-!
The threshold of a word of interval scheduling lowered to at most the total weight plus one,
as a word RAM program. No schedule has weight above the total weight, so the answer is kept,
and the threshold is then no larger than the other numbers of the word allow.
-/

namespace Lax434175Proofs.IsemClamp
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost Lax434175Proofs.IsemWords Lax434175Proofs.IsemPrograms
open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub)

/-- The word with its threshold lowered to at most the total weight plus one. -/
def clampW (u : List ℕ) : List ℕ := u.dropLast ++ [min (lastOf u) (totalW u (capN u) + 1)]

/-! ### On the words of instances -/

theorem totalW_append {y : List ℕ} {I : Instance} (h : EncodesInstance y I) (W : ℕ) :
    totalW (y ++ [W]) (capN (y ++ [W])) = Lax434175.IsemLink.totalWeight I := by
  have hlen := h.length_eq
  have hjc : jobCount (y ++ [W]) = I.jobs := by
    unfold jobCount; rw [getD_append_left (by omega)]; exact h.jobCount_eq
  have hn : capN (y ++ [W]) = I.jobs := by
    unfold capN; rw [hjc]; simp; omega
  rw [hn]
  unfold totalW Lax434175.IsemLink.totalWeight
  rw [listSum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← h.wt_eq j]
  unfold wt
  rw [hjc, getD_append_left (by have := j.isLt; omega), h.jobCount_eq]

theorem clampW_append {y : List ℕ} {I : Instance} (h : EncodesInstance y I) (W : ℕ) :
    clampW (y ++ [W]) = y ++ [min W (Lax434175.IsemLink.totalWeight I + 1)] := by
  unfold clampW
  rw [totalW_append h W, List.dropLast_concat]
  congr 3
  unfold lastOf
  simp

theorem clampW_encodes {x : List ℕ} {I : Instance} {W : ℕ} (hx : EncodesDecisionInstance x I W) :
    EncodesDecisionInstance (clampW x) I (min W (Lax434175.IsemLink.totalWeight I + 1)) := by
  obtain ⟨y, rfl, hy⟩ := hx
  exact ⟨y, clampW_append hy W, hy⟩

/-- Lowering the threshold to the total weight plus one keeps the answer. -/
theorem hasWeight_min (I : Instance) (W : ℕ) :
    I.HasWeight (min W (Lax434175.IsemLink.totalWeight I + 1)) ↔ I.HasWeight W := by
  rcases le_total W (Lax434175.IsemLink.totalWeight I + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    have hle : ∀ σ : I.Schedule, Instance.weight σ ≤ Lax434175.IsemLink.totalWeight I := fun σ =>
      Finset.sum_le_sum fun j _ => by cases σ j <;> simp
    constructor
    · rintro ⟨σ, -, hw⟩
      exact absurd (hw.trans (hle σ)) (by omega)
    · rintro ⟨σ, -, hw⟩
      exact absurd ((h.trans hw).trans (hle σ)) (by omega)

theorem clampW_le (u : List ℕ) : ∀ v ∈ clampW u, v ≤ Lax434175.Results.maxEntry u := by
  intro v hv
  unfold clampW at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact Lax434175Proofs.PadWord.le_foldr_max (List.dropLast_subset _ hv)
  · rw [List.mem_singleton.mp hv]
    exact (min_le_left _ _).trans (getD_le_max u _)

/-! ### The program -/

def clCom : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 0)) <|
  .seq (.ite (.lt (V "c") (V "L")) (.assign "n" (V "c")) (.assign "n" (V "L"))) <|
  .seq (.assign "s" (.lit 0)) <|
  .seq (forLoop "j" "n" sumBody) <|
  .seq (.assign "K" (.sub (V "L") (.lit 1))) <|
  .seq (forLoop "i" "K" copyBody) <|
  .seq (rdG "a" "L" "t" (V "K")) <|
  .seq (.assign "s" (.add (V "s") (.lit 1))) <|
  .seq (minTo "r" "t" "s") <|
  .write (V "r")

def clLayout : Layout := ⟨["L", "i", "v", "c", "n", "s", "j", "K", "t", "r"], ["a"], 6⟩

theorem clCom_ok : Com.Ok clLayout clCom := by
  simp [clCom, prelude, sumBody, copyBody, minTo, rdG, Lax434175Proofs.PadProgram.readLoop,
    Lax434175Proofs.PadProgram.below, Lax434175Proofs.PadProgram.incr, clLayout, Com.Ok, Cond.Ok,
    condExpr, Expr.Ok]

theorem run_cl (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndAT u) clCom (initEnv ext (u.length :: u)) σ'
      (80 * (u.length + 1)) ∧ σ'.out = clampW u := by
  have hBK0 : 4 * (u.length + Lax434175.Results.maxEntry u + 4) ≤ bndAT u := by
    have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bndAT; omega
  have hBLM0 : u.length * Lax434175.Results.maxEntry u + 4 * (u.length + Lax434175.Results.maxEntry u + 4)
      ≤ bndAT u := by
    unfold bndAT; nlinarith
  set L := u.length with hL
  set M := Lax434175.Results.maxEntry u with hM
  set B := bndAT u with hB
  have hBK : 4 * (L + M + 4) ≤ B := hBK0
  have hBLM : L * M + 4 * (L + M + 4) ≤ B := hBLM0
  have hMB : M < B := by omega
  have hLB : L < B := by omega
  obtain ⟨σ2, r1, ha, hL2, hout2, hz, -⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) hMB) (by omega)
  have hL2' : σ2.vars "L" = L := hL2
  refine ⟨fun _ => u.length + 2, ?_⟩
  set cv := u.getD 0 0 with hcv
  have rc := ev_rd ha hL2 (e := .lit 0) (evalB_lit (by omega)) hMB hLB "c"
  set s3 := σ2.setVar "c" cv with hs3
  have hcM : cv ≤ M := getD_le_max u 0
  set nv := min cv L with hnv
  have rn : Run B (.ite (.lt (V "c") (V "L")) (.assign "n" (V "c")) (.assign "n" (V "L"))) s3
      (s3.setVar "n" nv) 6 := by
    have hc3 : s3.vars "c" = cv := by simp [hs3]
    have hL3 : s3.vars "L" = L := by simp [hs3, hL2']
    have hc : (Cond.lt (V "c") (V "L")).evalB B s3 = some (decide (cv < L)) :=
      evalB_condLt (ev_var hc3 (by omega)) (ev_var hL3 hLB)
    by_cases hcl : cv < L
    · have e : nv = cv := by omega
      rw [e]
      exact (Run.ite_true (by rw [hc]; simp [hcl]) (Run.assign (ev_var hc3 (by omega)))).mono (by simp)
    · have e : nv = L := by omega
      rw [e]
      exact (Run.ite_false (by rw [hc]; simp [hcl]) (Run.assign (ev_var hL3 hLB))).mono (by simp)
  set s4 := (s3.setVar "n" nv).setVar "s" 0 with hs4
  have rs : Run B (.assign "s" (.lit 0)) (s3.setVar "n" nv) s4 2 := Run.assign (evalB_lit (by omega))
  let P : ℕ → Env → Prop := fun k τ => τ.vars "j" = k ∧ τ.vars "s" = totalW u k ∧ τ.vars "n" = nv ∧
    τ.vars "c" = cv ∧ τ.vars "L" = L ∧ τ.arrs = s4.arrs ∧ τ.out = []
  obtain ⟨s5, r5, ⟨-, hs5, -, -, hL5, ha5, hout5⟩⟩ := run_forLoop (B := B) "j" "n" sumBody nv 27 (by omega) P
    (fun k τ h => h.1) (fun k τ h => h.2.2.1)
    (fun k hk τ ⟨hj, hs, hn, hc, hLτ, haτ, hoτ⟩ => by
      have haτ' : τ.arrs "a" = arrW u := by rw [haτ]; simp [hs4, hs3, ha]
      have hkL : k < L := lt_of_lt_of_le hk (min_le_right _ _)
      have hidx : (Expr.add (.add (.lit 2) (.mul (.lit 2) (V "c"))) (V "j")).evalB B τ =
          some (2 + 2 * cv + k) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega))
          (ev_var hc (by omega)) (by omega)) (by omega)) (ev_var hj (by omega)) (by omega)
      have r1 := ev_rd haτ' hLτ hidx hMB hLB "v"
      have hw : u.getD (2 + 2 * cv + k) 0 = wt u k := rfl
      have hsum : totalW u k ≤ k * M := totalW_le u k
      have hwM : wt u k ≤ M := getD_le_max u _
      have hk1 : k * M + M ≤ L * M := by
        have := Nat.mul_le_mul_right M (show k + 1 ≤ L by omega); rw [Nat.succ_mul] at this; exact this
      have hsB : totalW u k + wt u k < B := by omega
      have e1 : (τ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).vars "s" = totalW u k := by simp [hs]
      have e2 : (τ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).vars "v" = wt u k := by
        simp only [vars_setVar]; exact hw
      have e3 : ((τ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).setVar "s" (totalW u k + wt u k)).vars "j" = k := by
        simp [hj]
      refine ⟨_, (r1.seq ((Run.assign (x := "s") (ev_add (ev_var e1 (by omega))
        (ev_var e2 (by omega)) hsB)).seq
        (Run.assign (x := "j") (ev_add (ev_var e3 (by omega)) (ev_lit (n := 1) (by omega))
          (by omega))))).mono (by simp),
        by simp, by simp [totalW_succ], by simp [hn], by simp [hc], by simp [hLτ], by simp [haτ],
        by simp [hoτ]⟩)
    (σ := s4) ⟨by simp, by simp [hs4, totalW], by simp [hs4], by simp [hs4, hs3], by simp [hs4, hs3, hL2'],
      by simp, by simp [hs4, hs3, hout2]⟩
  -- K := L - 1
  have hL5' : s5.vars "L" = L := hL5
  set s6 := s5.setVar "K" (L - 1) with hs6
  have rK : Run B (.assign "K" (.sub (V "L") (.lit 1))) s5 s6 6 :=
    (Run.assign (ev_sub (ev_var hL5' hLB) (ev_lit (by omega)))).mono (by simp)
  -- copy all but the last entry
  let Q : ℕ → Env → Prop := fun k τ => τ.vars "i" = k ∧ τ.vars "L" = L ∧ τ.vars "K" = L - 1 ∧
    τ.arrs "a" = arrW u ∧ τ.vars "s" = totalW u nv ∧ τ.out = (List.range k).map fun j => u.getD j 0
  obtain ⟨s7, r7, ⟨-, hL7, hK7, ha7, hs7, hout7⟩⟩ := run_forLoop (B := B) "i" "K" copyBody (L - 1) 7
    (by omega) Q (fun k τ h => h.1) (fun k τ h => h.2.2.1)
    (fun k hk τ ⟨hi, hLτ, hKτ, haτ, hsτ, hoτ⟩ => by
      have hget : (Expr.get "a" (V "i")).evalB B τ = some (u.getD k 0) :=
        evalB_get (ev_var hi (by omega))
          (by rw [haτ]; exact getElem?_arrOf _ (by omega)) (lt_of_le_of_lt (getD_le_max u k) hMB)
      refine ⟨_, ((Run.write hget).seq (Run.assign (x := "i") (v := k + 1)
        (by simp [hi]; omega))).mono (by simp), by simp, by simp [hLτ], by simp [hKτ], by simp [haτ],
        by simp [hsτ], ?_⟩
      simp [hoτ, List.range_succ])
    (σ := s6) ⟨by simp, by simp [hs6, hL5], by simp [hs6], by simp [hs6, ha5, hs4, hs3, ha],
      by simp [hs6, hs5], by simp [hs6, hout5]⟩
  -- t := the last entry
  have rt := ev_rd ha7 hL7 (e := V "K") (ev_var hK7 (by omega)) hMB hLB "t"
  set s8 := s7.setVar "t" (u.getD (L - 1) 0) with hs8
  have hS : totalW u nv + 1 < B := by
    have h1 : totalW u nv ≤ nv * M := totalW_le u nv
    have h2 : nv * M ≤ L * M := Nat.mul_le_mul_right _ (min_le_right _ _)
    omega
  have e8 : s8.vars "s" = totalW u nv := by simp [hs8, hs7]
  set s9 := s8.setVar "s" (totalW u nv + 1) with hs9
  have r9 : Run B (.assign "s" (.add (V "s") (.lit 1))) s8 s9 6 :=
    (Run.assign (ev_add (ev_var e8 (by omega)) (ev_lit (by omega)) hS)).mono (by simp)
  have ht9 : s9.vars "t" = u.getD (L - 1) 0 := by simp [hs9, hs8]
  have hs9' : s9.vars "s" = totalW u nv + 1 := by simp [hs9]
  have rm := run_minTo (x := "r") ht9 hs9' (lt_of_le_of_lt (getD_le_max u _) hMB) hS
  set s10 := s9.setVar "r" (min (u.getD (L - 1) 0) (totalW u nv + 1)) with hs10
  have hr10 : s10.vars "r" = min (u.getD (L - 1) 0) (totalW u nv + 1) := by simp [hs10]
  have rw11 : Run B (.write (V "r")) s10
      { s10 with out := s10.out ++ [min (u.getD (L - 1) 0) (totalW u nv + 1)] } 2 :=
    (Run.write (by rw [← hr10]; exact evalB_var (by rw [hr10]; omega))).mono (by simp)
  refine ⟨_, (r1.seq (rc.seq (rn.seq (rs.seq (r5.seq (rK.seq (r7.seq (rt.seq (r9.seq
    (rm.seq rw11)))))))))).mono ?_, ?_⟩
  · have : nv ≤ L := by omega
    simp only [Expr.size]
    omega
  · show s10.out ++ [min (u.getD (L - 1) 0) (totalW u nv + 1)] = clampW u
    have ho10 : s10.out = (List.range (L - 1)).map fun j => u.getD j 0 := by
      simp [hs10, hs9, hs8, hout7]
    rw [ho10, Lax434175Proofs.ThresholdProgram.map_range_getD u (by omega), ← List.dropLast_eq_take]
    rfl

/-- **Lowering the threshold is polynomial.** -/
theorem clampW_polytime : Lax759944.RamPolytime.RamPolytime clampW := by
  refine ramPolytime_of_runs clLayout clCom clampW bndAT (fun u => 80 * (u.length + 1)) 2001 1
    clCom_ok (fun u v hv => ?_) run_cl (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have h := sq_fit u 0 (by norm_num)
    have hM := Lax434175Proofs.IsemPrograms.getD_le_max u 0
    unfold bndAT
    rcases List.mem_cons.mp hv with rfl | hv
    · have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
        Nat.le_self_pow (by norm_num) _
      omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
        Nat.le_self_pow (by norm_num) _
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bndAT; have : 1 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit u 100 (by norm_num)
    refine le_trans ?_ (pow_mono_fit u (by norm_num))
    simp only [Layout.span, clLayout, List.length_cons, List.length_nil, bndAT]
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const, pow_one]
    omega
  · refine lt_of_lt_of_le ?_ (pow_mono_fit u (by norm_num))
    have h1 := clampW_le u v hv
    rcases Lax434175Proofs.PadReduction.foldr_max_mem_or_zero u with hm | hm
    · exact lt_of_le_of_lt h1 (entry_lt u (by unfold Lax434175.Results.maxEntry; exact hm))
    · have : v = 0 := by unfold Lax434175.Results.maxEntry at h1; omega
      rw [this]; exact Nat.two_pow_pos _

end Lax434175Proofs.IsemClamp
