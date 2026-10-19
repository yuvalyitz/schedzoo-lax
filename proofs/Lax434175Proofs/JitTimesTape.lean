import Mathlib.Tactic
import Lax434175Proofs.JitTimesWords
import Lax434175Proofs.JitTimesGather

/-!
On the tape of a standard word of `FF(1,m)||Σw_jZ_j`, the gathering program writes `n`, `m`,
for every job its two operation lengths, its weight and its due date, and the threshold
(`gatherOut_tape`): the records have the length `5m + 23` with the length in front, the two
operation lengths are entries `2` and `m + 2` of a record, and after the records come one empty
block, the six entries of the batch setup and three numbers per job.
-/

namespace Lax434175Proofs.JitTimesTape
open Lax434175 Lax434175.StandardReading
open Lax496464.FlowShop
open Lax434175Proofs.JitWords (machList transList recJ globJ)
open Lax434175Proofs.JitTimesWords Lax434175Proofs.JitTimesGather

/-- The numbers the algorithm needs: `n`, `m`, for every job its two operation lengths, its
weight and its due date, and the threshold. -/
def compact (J : Instance) (D : ℤ) : List ℕ :=
  [J.jobs, J.machines + 1] ++ (List.ofFn fun t => [J.p t, J.q t, J.w t, J.d t]).flatten ++ int D

/-- The tape of a word: its length, then the word. -/
def tape (u : List ℕ) : List ℕ := u.length :: u

theorem getD_flatten_ofFn {S : ℕ} : ∀ {n : ℕ} (f : Fin n → List ℕ), (∀ t, (f t).length = S) →
    ∀ (t : Fin n) (k : ℕ), k < S → (List.ofFn f).flatten.getD (t.val * S + k) 0 = (f t).getD k 0
  | 0, _, _, t, _, _ => t.elim0
  | n + 1, f, hf, t, k, hk => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun t' => ?_) t
    · simp only [Fin.val_zero, zero_mul, zero_add]
      exact List.getD_append _ _ _ _ (by rw [hf]; exact hk)
    · rw [Fin.val_succ, List.getD_append_right _ _ _ _ (by rw [hf]; nlinarith), hf,
        show (t'.val + 1) * S + k - S = t'.val * S + k by rw [add_mul, one_mul]; omega]
      exact getD_flatten_ofFn (fun i => f i.succ) (fun i => hf _) t' k hk

theorem length_flatten_ofFn {S : ℕ} {n : ℕ} (f : Fin n → List ℕ) (hf : ∀ t, (f t).length = S) :
    (List.ofFn f).flatten.length = n * S := by
  rw [List.length_flatten, List.map_ofFn]
  simp [Function.comp_def, hf]

theorem flatMap_range_eq {n : ℕ} (g : ℕ → List ℕ) :
    (List.range n).flatMap g = (List.ofFn fun t : Fin n => g t.val).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.ofFn_succ', List.concat_eq_append,
      List.flatten_append]; simp

variable (J : Instance) (D : ℤ)

theorem length_recJ (M p q : ℕ) : (recJ M p q).length + 1 = stride (M + 1) := by
  have h : (List.map ((fun a : List ℕ => a.length + 1) ∘ fun i => [1, i + 1]) (List.range M)).sum = M * 3 := by
    simp [Function.comp_def]
  simp [recJ, flat, machList, transList, stride]
  rw [h]; ring

/-- The records with their lengths. -/
abbrev recs : List ℕ :=
  (List.ofFn fun t => (recJ J.machines (J.p t) (J.q t)).length :: recJ J.machines (J.p t) (J.q t)).flatten

/-- The release dates, weights and due dates. -/
abbrev objs : List ℕ := (List.ofFn fun t => [0, J.w t, J.d t]).flatten

theorem length_recs : (recs J).length = J.jobs * stride (J.machines + 1) :=
  length_flatten_ofFn _ fun t => by simp only [List.length_cons]; exact length_recJ _ _ _

theorem std316_eq : std316 J = [0, J.jobs, J.machines + 1] ++ recs J ++ ([0] ++ globJ J.jobs ++ objs J) := by
  simp [std316]

theorem getD_rec (t : Fin J.jobs) (k : ℕ) (hk : k < stride (J.machines + 1)) :
    (tape (stdWord J D)).getD (4 + t.val * stride (J.machines + 1) + k) 0 =
      ((recJ J.machines (J.p t) (J.q t)).length :: recJ J.machines (J.p t) (J.q t)).getD k 0 := by
  have hlt : t.val * stride (J.machines + 1) + k < (recs J).length := by
    rw [length_recs]
    have := Nat.mul_le_mul_right (stride (J.machines + 1)) (show t.val + 1 ≤ J.jobs by omega)
    rw [add_mul, one_mul] at this; omega
  rw [show 4 + t.val * stride (J.machines + 1) + k = (t.val * stride (J.machines + 1) + k + 3) + 1 by ring]
  simp only [tape, List.getD_cons_succ]
  rw [show stdWord J D = [0, J.jobs, J.machines + 1] ++ (recs J ++ (([0] ++ globJ J.jobs ++ objs J) ++ int D))
      by simp [stdWord, std316_eq],
    show t.val * stride (J.machines + 1) + k + 3 = [0, J.jobs, J.machines + 1].length +
      (t.val * stride (J.machines + 1) + k) by simp; ring,
    List.getD_append_right _ _ _ _ (by simp), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hlt]
  exact getD_flatten_ofFn _ (fun t => by simp only [List.length_cons]; exact length_recJ _ _ _) t k hk

theorem getD_p (t : Fin J.jobs) :
    (tape (stdWord J D)).getD (6 + t.val * stride (J.machines + 1)) 0 = J.p t := by
  rw [show 6 + t.val * stride (J.machines + 1) = 4 + t.val * stride (J.machines + 1) + 2 by ring,
    getD_rec J D t 2 (by unfold stride; omega)]
  simp [recJ]

theorem getD_q (t : Fin J.jobs) :
    (tape (stdWord J D)).getD (6 + t.val * stride (J.machines + 1) + (J.machines + 1)) 0 = J.q t := by
  rw [show 6 + t.val * stride (J.machines + 1) + (J.machines + 1) =
      4 + t.val * stride (J.machines + 1) + (J.machines + 3) by ring,
    getD_rec J D t _ (by unfold stride; omega)]
  simp only [List.getD_cons_succ, recJ]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.getD_append_right _ _ _ _ (by simp), ← List.append_assoc,
    List.getD_append _ _ _ _ (by simp)]
  simp

theorem getD_obj (hn : 0 < J.jobs) (t : Fin J.jobs) (j : ℕ) (hj : j < 3) :
    (tape (stdWord J D)).getD (12 + J.jobs * stride (J.machines + 1) + 3 * t.val + j - 1) 0 =
      [0, J.w t, J.d t].getD j 0 := by
  have hg : (globJ J.jobs).length = 6 := by simp [globJ, show J.jobs ≠ 0 by omega]
  have hlo : (objs J).length = J.jobs * 3 := length_flatten_ofFn _ (fun _ => rfl)
  have hlt : t.val * 3 + j < (objs J).length := by
    rw [hlo]
    have := Nat.mul_le_mul_right 3 (show t.val + 1 ≤ J.jobs by omega)
    rw [add_mul, one_mul] at this; omega
  have hP : ([0, J.jobs, J.machines + 1] ++ recs J ++ [0] ++ globJ J.jobs).length =
      3 + J.jobs * stride (J.machines + 1) + 7 := by
    simp only [List.length_append, length_recs, hg]; simp
  rw [show 12 + J.jobs * stride (J.machines + 1) + 3 * t.val + j - 1 =
      ((3 + J.jobs * stride (J.machines + 1) + 7) + (t.val * 3 + j)) + 1 by omega]
  simp only [tape, List.getD_cons_succ]
  rw [show stdWord J D = ([0, J.jobs, J.machines + 1] ++ recs J ++ [0] ++ globJ J.jobs) ++ (objs J ++ int D)
      by simp [stdWord, std316_eq],
    List.getD_append_right _ _ _ _ (by rw [hP]; omega), hP, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hlt]
  exact getD_flatten_ofFn (S := 3) _ (fun _ => rfl) t j hj

theorem length_tape : (tape (stdWord J D)).length = (std316 J).length + 3 := by
  simp [tape, stdWord, int]

theorem getD_sign : (tape (stdWord J D)).getD ((tape (stdWord J D)).length - 2) 0 = (int D).getD 0 0 := by
  rw [length_tape]
  simp only [tape, show (std316 J).length + 3 - 2 = (std316 J).length + 1 by omega, List.getD_cons_succ,
    stdWord]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]

theorem getD_abs : (tape (stdWord J D)).getD ((tape (stdWord J D)).length - 1) 0 = (int D).getD 1 0 := by
  rw [length_tape]
  simp only [tape, show (std316 J).length + 3 - 1 = (std316 J).length + 1 + 1 by omega,
    List.getD_cons_succ, stdWord]
  rw [List.getD_append_right _ _ _ _ (by omega), show (std316 J).length + 1 - (std316 J).length = 1 by omega]

theorem getD_two : (tape (stdWord J D)).getD 2 0 = J.jobs := by
  simp [tape, stdWord, std316]

theorem getD_three : (tape (stdWord J D)).getD 3 0 = J.machines + 1 := by
  simp [tape, stdWord, std316]

/-- **The gathering program writes the numbers of the instance.** -/
theorem gatherOut_tape : gatherOut (tape (stdWord J D)) = compact J D := by
  unfold gatherOut compact
  rw [getD_two, getD_three, getD_sign, getD_abs, flatMap_range_eq]
  have hint : [(int D).getD 0 0, (int D).getD 1 0] = int D := by simp [int]
  rw [hint]
  congr 2
  refine congrArg List.flatten (List.ofFn_inj.mpr (funext fun t => ?_))
  have hn : 0 < J.jobs := Fin.pos t
  unfold jobNums
  rw [getD_p, getD_q]
  have hw := getD_obj J D hn t 1 (by omega)
  have hd := getD_obj J D hn t 2 (by omega)
  simp only [show 12 + J.jobs * stride (J.machines + 1) + 3 * t.val + 1 - 1 =
    12 + J.jobs * stride (J.machines + 1) + 3 * t.val by omega] at hw
  simp only [show 12 + J.jobs * stride (J.machines + 1) + 3 * t.val + 2 - 1 =
    13 + J.jobs * stride (J.machines + 1) + 3 * t.val by omega] at hd
  rw [hw, hd]
  rfl

end Lax434175Proofs.JitTimesTape
