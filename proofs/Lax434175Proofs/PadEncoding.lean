import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Lax434175Proofs.PadWord

/-!
The padded word encodes the padded instance.
-/

namespace Lax434175Proofs.PadEncoding

open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175.IsemLink Lax434175Proofs.PadProgram Lax434175Proofs.PadWord

theorem drop_two (a b : ℕ) (L : List ℕ) (k : ℕ) : (a :: b :: L).drop (2 + k) = L.drop k := by
  rw [show 2 + k = k + 1 + 1 by omega]; rfl

/-- The five blocks of a word assembled from five blocks. -/
theorem blocks_of (a b : ℕ) (A B C D E : List ℕ) (hA : A.length = a) (hB : B.length = a)
    (hC : C.length = a) (hD : D.length = a + 1) :
    P (a :: b :: (A ++ B ++ C ++ D ++ E)) = A ∧ Dl (a :: b :: (A ++ B ++ C ++ D ++ E)) = B ∧
      Wt (a :: b :: (A ++ B ++ C ++ D ++ E)) = C ∧ O (a :: b :: (A ++ B ++ C ++ D ++ E)) = D ∧
      T (a :: b :: (A ++ B ++ C ++ D ++ E)) = E := by
  have hn : nOf (a :: b :: (A ++ B ++ C ++ D ++ E)) = a := rfl
  have hL : A ++ B ++ C ++ D ++ E = A ++ (B ++ (C ++ (D ++ E))) := by simp
  have d1 : (A ++ (B ++ (C ++ (D ++ E)))).drop a = B ++ (C ++ (D ++ E)) := List.drop_left' hA
  have d2 : (A ++ (B ++ (C ++ (D ++ E)))).drop (a + a) = C ++ (D ++ E) := by
    rw [← List.drop_drop, d1, List.drop_left' hB]
  have d3 : (A ++ (B ++ (C ++ (D ++ E)))).drop (a + a + a) = D ++ E := by
    rw [← List.drop_drop, d2, List.drop_left' hC]
  have d4 : (A ++ (B ++ (C ++ (D ++ E)))).drop (a + a + a + (a + 1)) = E := by
    rw [← List.drop_drop, d3, List.drop_left' hD]
  simp only [P, Dl, Wt, O, T, hn]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (A ++ B ++ C ++ D ++ E).take a = A
    rw [hL]; exact List.take_left' hA
  · rw [drop_two, hL, d1]; exact List.take_left' hB
  · rw [drop_two, hL, show 2 * a = a + a by omega, d2]; exact List.take_left' hC
  · rw [drop_two, hL, show 3 * a = a + a + a by omega, d3]; exact List.take_left' hD
  · rw [show 3 + 4 * a = 2 + (a + a + a + (a + 1)) by omega, drop_two, hL, d4]

section Padded

variable {y : List ℕ} {I : Instance} (hy : EncodesInstance y I)
include hy

theorem os_mono : ∀ j < nOf y, os y j ≤ os y (j + 1) := fun j hj => by
  have := hy.offset_mono j (by rw [← hy.jobCount_eq]; exact hj)
  rwa [offset_eq y (by omega), offset_eq y (by omega)] at this

theorem os_mono' : ∀ a b, a ≤ b → b ≤ nOf y → os y a ≤ os y b := by
  intro a b hab hbn
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (ih (by omega) (by omega)).trans (os_mono hy b (by omega))

theorem os_zero : os y 0 = 0 := by
  have := hy.offset_zero
  rwa [offset_eq y (by omega)] at this

theorem os_last : os y (nOf y) = (T y).length := by
  rw [(split hy).2.2.2.2.2, offset_eq y le_rfl]; rfl

theorem blk_length {j : ℕ} (hj : j < nOf y) :
    (blk (os y) (T y) (machineCount y) j).length =
      if full (os y) j then os y (j + 1) - os y j else 1 := by
  unfold blk
  split
  · have hle := os_mono' hy (j + 1) (nOf y) (by omega) le_rfl
    rw [os_last hy] at hle
    simp
    omega
  · rfl

/-- The blocks of the first `k` jobs fill the first `os k + empties k` places. -/
theorem flatMap_length : ∀ k ≤ nOf y,
    ((List.range k).flatMap (blk (os y) (T y) (machineCount y))).length =
      os y k + empties (os y) k := by
  intro k hk
  induction k with
  | zero => simp [os_zero hy, empties]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega), empties_succ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [blk_length hy (by omega)]
    have := os_mono hy k (by omega)
    by_cases h : full (os y) k <;> simp only [h, ↓reduceIte] <;> (unfold full at h; omega)

/-- Where the block of job `j` sits among all blocks. -/
theorem blocks_getD {j r : ℕ} (hj : j < nOf y)
    (hr : r < (blk (os y) (T y) (machineCount y) j).length) :
    ((List.range (nOf y)).flatMap (blk (os y) (T y) (machineCount y))).getD
      (os y j + empties (os y) j + r) 0 = (blk (os y) (T y) (machineCount y) j).getD r 0 := by
  obtain ⟨k, hk⟩ : ∃ k, nOf y = j + 1 + k := ⟨nOf y - j - 1, by omega⟩
  have hsplit : List.range (nOf y) = List.range j ++ [j] ++
      (List.range k).map (fun i => j + 1 + i) := by
    rw [hk, List.range_add, List.range_succ]
  rw [hsplit, List.flatMap_append, List.flatMap_append, ← flatMap_length hy j (by omega)]
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.getD_append _ _ _ _ hr

/-- The block of a job is nonempty exactly if the job has an eligible machine. -/
theorem full_iff (j : Fin I.jobs) :
    full (os y) j ↔ (I.eligible j).Nonempty := by
  have hn : nOf y = I.jobs := hy.jobCount_eq
  have hj : (j : ℕ) < nOf y := by omega
  constructor
  · intro hf
    have hlt : os y j < os y (nOf y) := lt_of_lt_of_le hf (os_mono' hy _ _ (by omega) le_rfl)
    have hoff : offset y I.jobs = os y (nOf y) := by rw [← hn]; exact offset_eq y le_rfl
    have htl := hy.target_lt (os y j) (by rw [hoff]; exact hlt)
    refine ⟨⟨target y (os y j), htl⟩, (hy.eligible_iff j _).mpr ⟨os y j, ?_, ?_, rfl⟩⟩
    · rw [offset_eq y (by omega)]; rfl
    · rw [offset_eq y (by omega)]; exact hf
  · rintro ⟨i, hi⟩
    obtain ⟨t, h1, h2, _⟩ := (hy.eligible_iff j i).mp hi
    rw [offset_eq y (by omega)] at h1
    rw [offset_eq y (by omega)] at h2
    unfold full
    exact lt_of_le_of_lt h1 h2

/-- The padded weights. -/
abbrev wtOut : List ℕ :=
  (List.range (nOf y)).map (fun j => if full (os y) j then (Wt y).getD j 0 else 0)
/-- The shifted offsets. -/
abbrev offOut : List ℕ :=
  (List.range (nOf y)).map (fun j => os y j + empties (os y) j) ++
    [os y (nOf y) + empties (os y) (nOf y)]
/-- The blocks. -/
abbrev blOut : List ℕ := (List.range (nOf y)).flatMap (blk (os y) (T y) (machineCount y))

omit hy in
theorem padInst_eq : padInst y = nOf y :: (machineCount y + 1) ::
    (P y ++ Dl y ++ wtOut (y := y) ++ offOut (y := y) ++ blOut (y := y)) := rfl

theorem padInst_blocks :
    P (padInst y) = P y ∧ Dl (padInst y) = Dl y ∧ Wt (padInst y) = wtOut (y := y) ∧
      O (padInst y) = offOut (y := y) ∧ T (padInst y) = blOut (y := y) := by
  obtain ⟨_, hP, hD, _, _, _⟩ := split hy
  rw [padInst_eq]
  exact blocks_of _ _ _ _ _ _ _ hP hD (by simp) (by simp)

omit hy in
theorem offOut_getD {j : ℕ} (hj : j ≤ nOf y) :
    (offOut (y := y)).getD j 0 = os y j + empties (os y) j := by
  rcases Nat.lt_or_eq_of_le hj with h | h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · subst h
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

theorem blOut_length : (blOut (y := y)).length = os y (nOf y) + empties (os y) (nOf y) :=
  flatMap_length hy _ le_rfl

/-- The places of the block of job `j`. -/
theorem places_iff {j : ℕ} (hj : j < nOf y) (v : ℕ) :
    (∃ t, os y j + empties (os y) j ≤ t ∧ t < os y (j + 1) + empties (os y) (j + 1) ∧
        (blOut (y := y)).getD t 0 = v) ↔
      ∃ r < (blk (os y) (T y) (machineCount y) j).length,
        (blk (os y) (T y) (machineCount y) j).getD r 0 = v := by
  have hsucc : os y (j + 1) + empties (os y) (j + 1) =
      os y j + empties (os y) j + (blk (os y) (T y) (machineCount y) j).length := by
    rw [← flatMap_length hy j (by omega), ← flatMap_length hy (j + 1) (by omega),
      List.range_succ, List.flatMap_append, List.length_append]
    simp
  rw [hsucc]
  constructor
  · rintro ⟨t, h1, h2, h3⟩
    refine ⟨t - (os y j + empties (os y) j), by omega, ?_⟩
    rw [← blocks_getD hy hj (by omega), Nat.add_sub_cancel' h1]
    exact h3
  · rintro ⟨r, hr, h⟩
    exact ⟨os y j + empties (os y) j + r, by omega, by omega, (blocks_getD hy hj hr).trans h⟩

/-- Every entry of the blocks is a machine of the padding. -/
theorem blOut_lt (v : ℕ) (hv : v ∈ blOut (y := y)) : v < machineCount y + 1 := by
  obtain ⟨j, hj, hv⟩ := List.mem_flatMap.mp hv
  unfold blk at hv
  split at hv
  · have hvT : v ∈ T y := List.mem_of_mem_drop (List.mem_of_mem_take hv)
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hvT
    have htl := hy.target_lt t (by
      rw [← hy.jobCount_eq]; exact lt_of_lt_of_eq ht (split hy).2.2.2.2.2)
    rw [target_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht] at htl
    have := hy.machineCount_eq
    simp at htl
    omega
  · simp at hv
    omega

theorem offset_pad {j : ℕ} (hj : j ≤ nOf y) :
    offset (padInst y) j = os y j + empties (os y) j := by
  rw [offset_eq (padInst y) hj, (padInst_blocks hy).2.2.2.1, offOut_getD hj]

theorem target_pad (t : ℕ) : target (padInst y) t = (blOut (y := y)).getD t 0 := by
  rw [target_eq, (padInst_blocks hy).2.2.2.2]

theorem eligible_pad (j : Fin I.jobs) (i : Fin (I.machines + 1)) :
    i ∈ (pad I).eligible j ↔ ∃ t, offset (padInst y) j ≤ t ∧ t < offset (padInst y) (j + 1) ∧
      target (padInst y) t = i := by
  have hn : nOf y = I.jobs := hy.jobCount_eq
  have hj : (j : ℕ) < nOf y := by omega
  simp only [offset_pad hy (le_of_lt hj), offset_pad hy (Nat.succ_le_of_lt hj), target_pad hy]
  rw [places_iff hy hj]
  have hel : (pad I).eligible j = if (I.eligible j).Nonempty then
      (I.eligible j).map Fin.castSuccEmb else {Fin.last I.machines} := rfl
  by_cases hf : full (os y) j
  · have hne := (full_iff hy j).mp hf
    rw [hel, if_pos hne]
    have hblk : blk (os y) (T y) (machineCount y) j =
        ((T y).drop (os y j)).take (os y (j + 1) - os y j) := by unfold blk; rw [if_pos hf]
    have hlen : os y (j + 1) ≤ (T y).length :=
      (os_last hy) ▸ os_mono' hy _ _ (by omega) le_rfl
    have hget : ∀ r < os y (j + 1) - os y j,
        (((T y).drop (os y j)).take (os y (j + 1) - os y j)).getD r 0 = target y (os y j + r) := by
      intro r hr
      rw [getD_take _ _ _ hr, getD_drop, target_eq]
    rw [hblk]
    have hlen' : (((T y).drop (os y j)).take (os y (j + 1) - os y j)).length =
        os y (j + 1) - os y j := by simp; omega
    rw [hlen']
    constructor
    · intro hi
      obtain ⟨i0, hi0, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨t, h1, h2, h3⟩ := (hy.eligible_iff j i0).mp hi0
      rw [offset_eq y (by omega)] at h1
      rw [offset_eq y (by omega)] at h2
      refine ⟨t - os y j, by unfold os at *; omega, ?_⟩
      rw [hget _ (by unfold os at *; omega), show os y j + (t - os y j) = t by unfold os at *; omega,
        h3]
      rfl
    · rintro ⟨r, hr, h⟩
      rw [hget r hr] at h
      have hlt : target y (os y j + r) < I.machines := by
        apply hy.target_lt
        have hoff : offset y I.jobs = os y (nOf y) := by rw [← hn]; exact offset_eq y le_rfl
        refine lt_of_lt_of_eq ?_ hoff.symm
        have := os_mono' hy (j + 1) (nOf y) (by omega) le_rfl
        unfold os at *
        omega
      refine Finset.mem_map.mpr ⟨⟨target y (os y j + r), hlt⟩,
        (hy.eligible_iff j _).mpr ⟨os y j + r, ?_, ?_, rfl⟩, Fin.ext h⟩
      · rw [offset_eq y (by omega)]; unfold os; omega
      · rw [offset_eq y (by omega)]; unfold os at *; omega
  · have hne : ¬ (I.eligible j).Nonempty := fun h => hf ((full_iff hy j).mpr h)
    rw [hel, if_neg hne]
    have hblk : blk (os y) (T y) (machineCount y) j = [machineCount y] := by
      unfold blk; rw [if_neg hf]
    rw [hblk]
    show i ∈ ({Fin.last I.machines} : Finset (Fin (I.machines + 1))) ↔ _
    rw [Finset.mem_singleton]
    have hm : machineCount y = I.machines := hy.machineCount_eq
    constructor
    · rintro rfl
      exact ⟨0, by simp, by simp [hm]⟩
    · rintro ⟨r, hr, h⟩
      have : r = 0 := by simpa using hr
      subst this
      apply Fin.ext
      rw [Fin.val_last]
      simp at h
      omega

/-- **The padded word encodes the padded instance.** -/
theorem encodes_pad : EncodesInstance (padInst y) (pad I) where
  jobCount_eq := hy.jobCount_eq
  machineCount_eq := by
    show machineCount y + 1 = I.machines + 1
    rw [hy.machineCount_eq]
  length_eq := by
    obtain ⟨_, hP, hD, _, _, _⟩ := split hy
    have hn : nOf y = I.jobs := hy.jobCount_eq
    show (padInst y).length = 3 + 4 * I.jobs + offset (padInst y) I.jobs
    rw [← hn, offset_pad hy le_rfl]
    have hL : (padInst y).length = 2 + nOf y + nOf y + nOf y + (nOf y + 1) +
        (blOut (y := y)).length := by
      rw [padInst_eq]; simp [hP, hD]; omega
    rw [hL, blOut_length hy]
    omega
  proc_eq := fun j => by
    have hj : (j : ℕ) < nOf (padInst y) := by
      have h : nOf y = I.jobs := hy.jobCount_eq
      show (j : ℕ) < nOf y; rw [h]; exact j.isLt
    rw [proc_eq _ hj, (padInst_blocks hy).1, ← proc_eq y hj]
    exact hy.proc_eq j
  due_eq := fun j => by
    have hj : (j : ℕ) < nOf (padInst y) := by
      have h : nOf y = I.jobs := hy.jobCount_eq
      show (j : ℕ) < nOf y; rw [h]; exact j.isLt
    rw [due_eq _ hj, (padInst_blocks hy).2.1, ← due_eq y hj]
    exact hy.due_eq j
  wt_eq := fun j => by
    have hj : (j : ℕ) < nOf (padInst y) := by
      have h : nOf y = I.jobs := hy.jobCount_eq
      show (j : ℕ) < nOf y; rw [h]; exact j.isLt
    rw [wt_eq _ hj, (padInst_blocks hy).2.2.1]
    show _ = if (I.eligible j).Nonempty then I.w j else 0
    have hj' : (j : ℕ) < nOf y := hj
    simp only [wtOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj',
      Option.map_some, Option.getD_some]
    by_cases hf : full (os y) j
    · rw [if_pos hf, if_pos ((full_iff hy j).mp hf), ← List.getD_eq_getElem?_getD, ← wt_eq y hj']
      exact hy.wt_eq j
    · rw [if_neg hf, if_neg (fun h => hf ((full_iff hy j).mpr h))]
  offset_zero := by
    rw [offset_pad hy (Nat.zero_le _), os_zero hy]; rfl
  offset_mono := fun j hj => by
    have hn : nOf y = I.jobs := hy.jobCount_eq
    have hj : j < I.jobs := hj
    rw [offset_pad hy (by omega), offset_pad hy (by omega), empties_succ]
    have := os_mono hy j (by omega)
    split <;> omega
  target_lt := fun t ht => by
    have hn : nOf y = I.jobs := hy.jobCount_eq
    rw [target_pad hy]
    show _ < I.machines + 1
    rw [← hy.machineCount_eq]
    have ht' : t < (blOut (y := y)).length := by
      rw [blOut_length hy, ← offset_pad hy le_rfl, hn]; exact ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
    exact blOut_lt hy _ (List.getElem_mem ht')
  eligible_iff := eligible_pad hy

end Padded

end Lax434175Proofs.PadEncoding
