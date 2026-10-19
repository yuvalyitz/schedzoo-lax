import Mathlib.Tactic
import Lax434175Proofs.JitEmitMain

/-!
The numbers of the standard word of the construction are at most a fixed multiple of the fourth
power of its length: a due date is below `g² Q + (2g + 1) Q + n + 1`, where `g ≤ R m` and
`Q < (n + 1)²`, while the word has more than `2 R m n` jobs.
-/

namespace Lax434175Proofs.JitSmall
open Lax434175Proofs.JitRaw Lax434175Proofs.JitWords Lax434175Proofs.JitEmit
open Lax496464.HittingSet Lax496464.Construction

variable (P : Instance) (k : ℕ)

theorem mem_memberList {p : ℕ × ℕ} (hp : p ∈ memberList P) : p.1 < P.m ∧ p.2 < P.n := by
  unfold memberList at hp
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at hp
  obtain ⟨j, i, -, rfl⟩ := hp
  exact ⟨j.isLt, i.isLt⟩

theorem memberList_nil (hm : P.m = 0) : memberList P = [] := by
  unfold memberList
  have : List.finRange P.m = [] := by rw [List.finRange_eq_nil_iff]; exact hm
  rw [this]; rfl

/-- The slot of a job lies in range. -/
theorem slot_lt {t : ℕ} (ht : t < (ofHS P k).numJobs) :
    (ofHS P k).seg t < (ofHS P k).R ∧ (ofHS P k).setIdx t < P.m ∧ (ofHS P k).elem t < P.n := by
  set x := ofHS P k with hx
  have hxm : x.m = P.m := rfl
  have hxn : x.n = P.n := rfl
  have hxL : x.ML = memberList P := rfl
  unfold HRaw.seg HRaw.setIdx HRaw.elem HRaw.slot
  by_cases h1 : t < x.selCount
  · rw [if_pos h1]
    have hl : 0 < x.ML.length := by
      rcases Nat.eq_zero_or_pos x.ML.length with h0 | h0
      · simp [HRaw.selCount, h0] at h1
      · exact h0
    have hmem := mem_memberList P (Bnd.mem_ML (x := x) (t := t) hl)
    refine ⟨?_, hmem.1, hmem.2⟩
    dsimp only
    unfold HRaw.selCount at h1
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
  · rw [if_neg h1]
    dsimp only
    have hN : t < x.selCount + 2 * x.dumCount := ht
    set v := if t - x.selCount < x.dumCount then t - x.selCount else t - x.selCount - x.dumCount
      with hv
    have hvd : v < x.dumCount := by rw [hv]; split_ifs <;> omega
    have hD : x.dumCount = x.R * (x.m * x.n) := by unfold HRaw.dumCount; ring
    rw [hD] at hvd
    have hmn : 0 < x.m * x.n := by
      rcases Nat.eq_zero_or_pos (x.m * x.n) with h0 | h0
      · rw [h0] at hvd; simp at hvd
      · exact h0
    have hn : 0 < x.n := Nat.pos_of_mul_pos_left hmn
    refine ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hvd), ?_, Nat.mod_lt _ hn⟩
    have h := Nat.mod_lt v hmn
    refine Nat.div_lt_of_lt_mul ?_
    rw [show x.n * P.m = x.m * x.n by rw [hxm]; ring]
    exact h

/-- With a job, the number of jobs bounds the universe and the epochs. -/
theorem jobs_big {t : ℕ} (ht : t < (ofHS P k).numJobs) (hk : 2 ≤ k) (hkn : k ≤ P.n) :
    P.n ≤ (ofHS P k).numJobs ∧ (ofHS P k).R * P.m ≤ (ofHS P k).numJobs := by
  set x := ofHS P k with hx
  have hm : 1 ≤ P.m := by
    rcases Nat.eq_zero_or_pos P.m with h0 | h0
    · exfalso
      have hL : x.ML = [] := memberList_nil P h0
      have : x.numJobs = 0 := by
        show x.R * x.ML.length + 2 * (x.R * P.m * P.n) = 0
        rw [hL, h0]; simp
      omega
    · exact h0
  have hR : 2 ≤ x.R := by unfold HRaw.R; omega
  have hN : x.numJobs = x.selCount + 2 * (x.R * P.m * P.n) := rfl
  constructor
  · have : P.n ≤ x.R * P.m * P.n := by
      have : 1 ≤ x.R * P.m := by nlinarith
      nlinarith
    omega
  · have : x.R * P.m ≤ x.R * P.m * P.n := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem mem_rec {k p q v : ℕ} (h : v ∈ (recJ k p q).length :: recJ k p q) :
    v ≤ 5 * k + 27 ∨ v = p ∨ v = q := by
  have ht : ∀ w ∈ recTail, w ≤ 4 := by decide
  rw [recJ_eq, List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_append] at h
    rcases h with h | h
    · simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at h
      omega
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp h
      simp only [List.mem_range] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      omega
  · have := ht v h; omega

/-- **Every number of the word is at most `64` times the fourth power of the number of jobs
plus one, plus the word's small constants.** -/
theorem entry_le (hk : 2 ≤ k) (hkn : k ≤ P.n) (hn : P.n ≤ 4 + P.m + ∑ j : Fin P.m, (P.F j).card) :
    ∀ v ∈ (ofHS P k).stdW, v ≤ 64 * ((ofHS P k).numJobs + 1) ^ 4 := by
  set x := ofHS P k with hx
  set N := x.numJobs with hN
  have hxk : x.k = k := rfl
  have hxn : x.n = P.n := rfl
  have hxm : x.m = P.m := rfl
  have hP4 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hN4 : N + 1 ≤ (N + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  -- the solution size is small
  have hkN : k + 1 ≤ N + 5 := by
    by_cases hm : P.m = 0
    · have : ∑ j : Fin P.m, (P.F j).card = 0 := by
        rw [Finset.sum_eq_zero]; intro j; exact absurd j.isLt (by omega)
      omega
    · have hm1 : 1 ≤ P.m := by omega
      have hR : 2 ≤ x.R := by unfold HRaw.R; omega
      have : P.n ≤ x.R * P.m * P.n := by
        have : 1 ≤ x.R * P.m := by nlinarith
        nlinarith
      have : N = x.selCount + 2 * (x.R * P.m * P.n) := rfl
      omega
  -- the numbers of a job
  have hjob : ∀ t < N, x.jp t ≤ 64 * (N + 1) ^ 4 ∧ x.jq t ≤ 64 * (N + 1) ^ 4 ∧
      x.jd t ≤ 64 * (N + 1) ^ 4 := by
    intro t ht
    obtain ⟨hs, hj, he⟩ := slot_lt P k ht
    obtain ⟨hnN, hRm⟩ := jobs_big P k ht hk hkn
    rw [← hx] at hs hj he hnN hRm
    set gg := x.g (x.seg t) (x.setIdx t) with hgg
    have hg : gg ≤ N := by
      have : gg ≤ x.R * P.m := by
        rw [hgg]; unfold HRaw.g
        have : x.seg t * P.m + P.m ≤ x.R * P.m := by
          have := Nat.mul_le_mul_right P.m (show x.seg t + 1 ≤ x.R by omega)
          linarith
        rw [hxm]; omega
      omega
    have hQ : x.Q ≤ (N + 1) ^ 2 := by
      unfold HRaw.Q
      rw [hxk, hxn]
      calc (k - 1) * (P.n + 1) ≤ (N + 1) * (N + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (N + 1) ^ 2 := by ring
    have e1 : gg * (P.n + 1) ≤ (N + 1) ^ 2 := by
      calc gg * (P.n + 1) ≤ (N + 1) * (N + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (N + 1) ^ 2 := by ring
    have e2 : (2 * gg + 1) * x.Q ≤ 2 * (N + 1) ^ 3 := by
      calc (2 * gg + 1) * x.Q ≤ (2 * (N + 1)) * (N + 1) ^ 2 := Nat.mul_le_mul (by omega) hQ
        _ = 2 * (N + 1) ^ 3 := by ring
    have e3 : (gg + 1) * x.Q ≤ (N + 1) ^ 3 := by
      calc (gg + 1) * x.Q ≤ (N + 1) * (N + 1) ^ 2 := Nat.mul_le_mul (by omega) hQ
        _ = (N + 1) ^ 3 := by ring
    have e4 : gg * x.Q ≤ (N + 1) ^ 3 := le_trans (Nat.mul_le_mul_right _ (by omega)) e3
    have e5 : x.G (x.seg t) (x.setIdx t) ≤ (N + 1) ^ 4 := by
      unfold HRaw.G
      rw [← hgg]
      calc gg ^ 2 * x.Q ≤ (N + 1) ^ 2 * (N + 1) ^ 2 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) hQ
        _ = (N + 1) ^ 4 := by ring
    have h23 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h33 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · unfold HRaw.jp; rw [← hgg, hxn]; split_ifs <;> omega
    · unfold HRaw.jq; rw [← hgg]; split_ifs <;> omega
    · unfold HRaw.jd; rw [← hgg]; split_ifs <;> omega
  intro v hv
  unfold HRaw.stdW at hv
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hv
  rcases hv with (((((h | h | h) | ⟨t, ht, h⟩) | h) | h) | ⟨t, ht, h⟩) | h
  · omega
  · omega
  · rw [h, hxk]; omega
  · obtain ⟨hp, hq, -⟩ := hjob t ht
    unfold HRaw.recW at h
    rcases mem_rec h with h | h | h
    · rw [hxk] at h; omega
    · omega
    · omega
  · omega
  · unfold globJ at h; split_ifs at h <;> simp at h <;> omega
  · obtain ⟨-, -, hd⟩ := hjob t ht
    unfold HRaw.dueW at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h <;> omega
  · have hT : x.target ≤ 2 * (N + 1) ^ 2 := by
      by_cases hm : P.m = 0
      · simp [HRaw.target, hxm, hm]
      · have hm1 : 1 ≤ P.m := by omega
        have hR : 2 ≤ x.R := by unfold HRaw.R; omega
        have hRmN : x.R * P.m ≤ N := by
          have : x.R * P.m ≤ x.R * P.m * P.n := Nat.le_mul_of_pos_right _ (by omega)
          have : N = x.selCount + 2 * (x.R * P.m * P.n) := rfl
          omega
        have hnN : P.n ≤ N := by
          have : P.n ≤ x.R * P.m * P.n := by
            have : 1 ≤ x.R * P.m := by nlinarith
            nlinarith
          have : N = x.selCount + 2 * (x.R * P.m * P.n) := rfl
          omega
        unfold HRaw.target
        rw [hxm, hxk]
        calc x.R * P.m * (2 * k - 1) ≤ (N + 1) * (2 * (N + 1)) :=
              Nat.mul_le_mul (by omega) (by omega)
          _ = 2 * (N + 1) ^ 2 := by ring
    have h23 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    unfold HRaw.thrW at h
    split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with h | h <;> omega

theorem length_ge : 3 * (ofHS P k).numJobs ≤ (ofHS P k).stdW.length := by
  unfold HRaw.stdW
  simp only [List.length_append]
  have : ((List.range (ofHS P k).numJobs).flatMap (ofHS P k).dueW).length = 3 * (ofHS P k).numJobs := by
    rw [List.length_flatMap]; simp [HRaw.dueW, List.sum_replicate, Nat.mul_comm]
  omega

/-- **The word is small.** -/
theorem small (hk : 2 ≤ k) (hkn : k ≤ P.n) (hn : P.n ≤ 4 + P.m + ∑ j : Fin P.m, (P.F j).card) :
    (ofHS P k).stdW ∈ Lax434175.Results.Small 64 4 := by
  intro v hv
  have h1 := entry_le P k hk hkn hn v hv
  have h2 := length_ge P k
  have : ((ofHS P k).numJobs + 1) ^ 4 ≤ ((ofHS P k).stdW.length + 1) ^ 4 :=
    Nat.pow_le_pow_left (by omega) 4
  omega

end Lax434175Proofs.JitSmall
