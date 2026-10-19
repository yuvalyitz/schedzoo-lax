import Mathlib.Tactic
import Lax434175Proofs.JitTimesMap

/-!
The parameters of an instance of `FF(1,m)||Σw_jZ_j` read off its data (`n`, `m`, `W`, `q_max`,
`χ`, positive last operations), and bounds on the numbers of the words the algorithm passes
through, in terms of the length and the largest number of the standard word.
-/

namespace Lax434175Proofs.JitTimesFacts
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.StandardReading
open Lax434175.ResultParameters Lax434175.JitFlowShop
open Lax496464.FlowShop
open Lax434175Proofs.JitTimesWords Lax434175Proofs.JitTimesSem Lax434175Proofs.JitTimesTape
open Lax434175Proofs.JitTimesGather

/-! ### The parameters -/

section Params

variable (x : Inst OperationsFamily.family ZooShops.p316)

theorem lastTime_eq (j : Fin x.base.jobs) : Ops.lastTime x.base j = (jOf x).q j := by
  have h2 := ops_eq x j
  unfold Ops.lastTime
  rw [dif_pos (by omega)]
  unfold Operations.opTime
  rw [dif_pos (machines_pos x)]
  show x.base.p j ⟨x.base.ops j - 1, _⟩ ⟨0, _⟩ = x.base.p j (op1 x j) ⟨0, _⟩
  congr 1
  exact Fin.ext (by simp [op1, h2])

theorem n_eq : Ops.n ZooShops.p316 x = (jOf x).jobs := rfl

theorem m_eq : Ops.m ZooShops.p316 x = (jOf x).machines + 1 := (jOf_machines x).symm

theorem totalW_eq : Ops.totalW ZooShops.p316 x = totalWeight (jOf x) := rfl

theorem qmax_eq : Ops.qmax ZooShops.p316 x = Finset.univ.sup (jOf x).q := by
  unfold Ops.qmax
  congr 1
  exact funext (lastTime_eq x)

theorem chi_eq : Ops.chi ZooShops.p316 x = overlapJ (jOf x) := by
  unfold Ops.chi overlapJ
  congr 2
  funext j
  rw [lastTime_eq]
  rfl

theorem lastPositive_iff : Ops.lastPositive ZooShops.p316 x ↔ ∀ j, 0 < (jOf x).q j := by
  unfold Ops.lastPositive
  exact forall_congr' fun j => by rw [lastTime_eq]

end Params

/-! ### The numbers of the words -/

section Numbers

variable (J : Instance) (D : ℤ)

/-- The bound on the numbers: the length and the largest number of the standard word. -/
abbrev Zb : ℕ := (stdWord J D).length + Lax434175.Results.maxEntry (stdWord J D)

theorem tape_le (i : ℕ) : (tape (stdWord J D)).getD i 0 ≤ Zb J D := by
  rcases i with _ | i
  · simp [tape]
  · simp only [tape, List.getD_cons_succ]
    have := Lax434175Proofs.IsemPrograms.getD_le_max (stdWord J D) i
    show _ ≤ (stdWord J D).length + _
    omega

theorem jobs_le : J.jobs ≤ Zb J D := by have := tape_le J D 2; rwa [getD_two] at this
theorem machines_le : J.machines + 1 ≤ Zb J D := by have := tape_le J D 3; rwa [getD_three] at this
theorem p_le (t : Fin J.jobs) : J.p t ≤ Zb J D := by
  have := tape_le J D (6 + t.val * stride (J.machines + 1)); rwa [JitTimesTape.getD_p] at this
theorem q_le (t : Fin J.jobs) : J.q t ≤ Zb J D := by
  have := tape_le J D (6 + t.val * stride (J.machines + 1) + (J.machines + 1)); rwa [JitTimesTape.getD_q] at this

theorem w_le (t : Fin J.jobs) : J.w t ≤ Zb J D := by
  have h := getD_obj J D (Fin.pos t) t 1 (by omega)
  have := tape_le J D (12 + J.jobs * stride (J.machines + 1) + 3 * t.val + 1 - 1)
  rw [h] at this; simpa using this

theorem d_le (t : Fin J.jobs) : J.d t ≤ Zb J D := by
  have h := getD_obj J D (Fin.pos t) t 2 (by omega)
  have := tape_le J D (12 + J.jobs * stride (J.machines + 1) + 3 * t.val + 2 - 1)
  rw [h] at this; simpa using this

theorem abs_le : D.natAbs ≤ Zb J D := by
  have := tape_le J D ((tape (stdWord J D)).length - 1); rw [getD_abs] at this; simpa [int] using this

theorem sum_le_mul {n : ℕ} (g : Fin n → ℕ) (b : ℕ) (h : ∀ t, g t ≤ b) : ∑ t, g t ≤ n * b := by
  calc ∑ t, g t ≤ ∑ _t : Fin n, b := Finset.sum_le_sum fun t _ => h t
    _ = n * b := by simp

theorem totalWeight_le : totalWeight J ≤ Zb J D * Zb J D :=
  (sum_le_mul _ _ (w_le J D)).trans (Nat.mul_le_mul_right _ (jobs_le J D))

theorem bigK_le : bigK J ≤ 2 * (Zb J D * Zb J D) + 1 := by
  have := sum_le_mul (fun t => J.d t + J.q t) (2 * Zb J D) fun t => by
    have := d_le J D t; have := q_le J D t; omega
  have h2 : J.jobs * (2 * Zb J D) ≤ Zb J D * (2 * Zb J D) := Nat.mul_le_mul_right _ (jobs_le J D)
  unfold bigK; nlinarith

/-- Every number of the compact word is at most the bound. -/
theorem compact_le : ∀ v ∈ compact J D, v ≤ Zb J D := by
  intro v hv
  simp only [compact, List.mem_append, List.mem_cons, List.mem_flatten, List.mem_ofFn,
    List.not_mem_nil, or_false, int] at hv
  rcases hv with ((rfl | rfl) | ⟨l, ⟨t, rfl⟩, hl⟩) | (rfl | rfl)
  · exact jobs_le J D
  · exact machines_le J D
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact p_le J D t
    · exact q_le J D t
    · exact w_le J D t
    · exact d_le J D t
  · split_ifs <;> have := jobs_le J D <;> have := machines_le J D <;> omega
  · exact abs_le J D

theorem maxEntry_compact : Lax434175.Results.maxEntry (compact J D) ≤ Zb J D := by
  unfold Lax434175.Results.maxEntry
  rcases Lax434175Proofs.PadReduction.foldr_max_mem_or_zero (compact J D) with h | h
  · exact compact_le J D _ h
  · rw [h]; exact Nat.zero_le _

/-- Every number of the word of lax-496464 is at most `4 Z³`. -/
theorem theirWord_le : ∀ v ∈ theirWord J D, v ≤ 4 * (Zb J D + 1) ^ 3 := by
  have hZ3 : (Zb J D + 1) * (Zb J D + 1) ≤ (Zb J D + 1) ^ 3 := by
    rw [pow_succ, pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hZZ : Zb J D * Zb J D + 1 ≤ (Zb J D + 1) * (Zb J D + 1) := by nlinarith
  have hZ1 : Zb J D + 1 ≤ (Zb J D + 1) * (Zb J D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hK := bigK_le J D
  have hn := jobs_le J D
  have hdK : ∀ t : Fin J.jobs, (t.val + 2) * bigK J ≤ 4 * (Zb J D + 1) ^ 3 := fun t => by
    have h1 : (t.val + 2) * bigK J ≤ (Zb J D + 1) * (2 * (Zb J D * Zb J D) + 1) :=
      Nat.mul_le_mul (by have := t.isLt; omega) hK
    have h2 : (Zb J D + 1) * (2 * (Zb J D * Zb J D) + 1) ≤ (Zb J D + 1) * (2 * ((Zb J D + 1) * (Zb J D + 1))) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : (Zb J D + 1) * (2 * ((Zb J D + 1) * (Zb J D + 1))) = 2 * (Zb J D + 1) ^ 3 := by ring
    exact h1.trans (h2.trans (h3.le.trans (by omega)))
  intro v hv
  unfold theirWord at hv
  by_cases h0 : J.jobs = 0
  · rw [if_pos h0] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h <;> (try split_ifs at h) <;> omega
  rw [if_neg h0] at hv
  by_cases h1 : J.machines = 0 ∨ D < 0
  · rw [if_pos h1] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h <;> omega
  rw [if_neg h1] at hv
  by_cases h2 : (totalWeight J : ℤ) ≤ D
  · rw [if_pos h2] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h <;> omega
  rw [if_neg h2] at hv
  simp only [wordOf, theirInst, cap, dummy, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false] at hv
  have hW := totalWeight_le J D
  rcases hv with (((((rfl | rfl) | ⟨t, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩) | rfl
  · omega
  · have := min_le_right J.machines J.jobs; omega
  · have := p_le J D t; omega
  · have := q_le J D t; omega
  · split_ifs
    · exact hdK t
    · have := d_le J D t; omega
  · split_ifs
    · omega
    · have := w_le J D t; omega
  · omega

theorem length_theirWord : (theirWord J D).length ≤ 4 * J.jobs + 3 := by
  unfold theirWord
  split_ifs <;> simp [length_wordOf, theirInst, cap, dummy] <;> omega

end Numbers

end Lax434175Proofs.JitTimesFacts
