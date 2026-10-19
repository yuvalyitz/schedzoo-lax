import Mathlib.Tactic
import Lax434175Proofs.IsemStandard
import Lax434175Proofs.ThresholdProgram

/-!
The two word maps from the words of interval scheduling to the standard words of
`P|M_j|Σ w_j Z_j`, as functions on all words: `compressWord` drops the machines no job
may use, `stdOfWord` writes the standard word. Every loop bound is capped by the
length of the word, so the maps are polynomial on every word; on the words of
instances the caps change nothing.
-/

namespace Lax434175Proofs.IsemWords
open Lax434175 Lax434175.IsemLink Lax434175.StandardReading
open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175Proofs.IsemStandard

-- Reading a decision word

/-- The threshold: the last number. -/
def lastOf (y : List ℕ) : ℕ := y.getD (y.length - 1) 0

/-- The number of jobs, capped by the length. -/
def capN (y : List ℕ) : ℕ := min (jobCount y) y.length

/-- The number of machines, capped by the length. -/
def capM (y : List ℕ) : ℕ := min (machineCount y) y.length

/-- Whether the block of job `j` lists machine `i`. -/
def inBlock (y : List ℕ) (j i : ℕ) : Bool :=
  (List.range (min (offset y (j + 1)) y.length)).any fun t => decide (offset y j ≤ t) && decide (target y t = i)

-- The standard word

/-- The machines job `j` may use, as the tuples `[0, i]`, increasing. -/
def machListW (y : List ℕ) (m j : ℕ) : List (List ℕ) :=
  ((List.range m).filter (inBlock y j)).map fun i => [0, i]

/-- The record of job `j`. -/
def recW (y : List ℕ) (m j : ℕ) : List ℕ :=
  [1] ++ List.replicate m (proc y j) ++ [0] ++ flat (machListW y m j) ++ [0] ++ [1, 3, 0, 0, 0] ++ [0]

/-- The total weight of the first `n` jobs. -/
def totalW (y : List ℕ) (n : ℕ) : ℕ := ((List.range n).map (wt y)).sum

/-- `S - W` as sign and absolute value. -/
def diffWord (S W : ℕ) : List ℕ := [if S < W then 1 else 0, if S < W then W - S else S - W]

/-- **The standard word** of the instance and threshold of a word of interval scheduling. -/
def stdOfWord (y : List ℕ) : List ℕ :=
  [0, capN y, capM y] ++ (List.range (capN y)).flatMap (fun j => (recW y (capM y) j).length :: recW y (capM y) j) ++
    [0] ++ (if capN y = 0 then [0] else [1, 4, 1, 0, 0, 0]) ++
    (List.range (capN y)).flatMap (fun j => [0, wt y j, due y j]) ++ diffWord (totalW y (capN y)) (lastOf y)

-- Correctness on the words of instances

theorem getD_append_left {y : List ℕ} {W p : ℕ} (h : p < y.length) :
    (y ++ [W]).getD p 0 = y.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

variable {y0 : List ℕ} {J : Instance} {W : ℕ}

theorem len_eq (h : EncodesInstance y0 J) : y0.length = 3 + 4 * J.jobs + offset y0 J.jobs :=
  h.length_eq

theorem offset_le (h : EncodesInstance y0 J) : ∀ {j k : ℕ}, j ≤ k → k ≤ J.jobs →
    offset y0 j ≤ offset y0 k
  | j, 0, hjk, _ => by rw [Nat.le_zero.mp hjk]
  | j, k + 1, hjk, hk => by
    rcases Nat.of_le_succ hjk with h1 | h1
    · exact (offset_le h h1 (by omega)).trans (h.offset_mono k (by omega))
    · rw [h1]

theorem offset_le_last (h : EncodesInstance y0 J) {j : ℕ} (hj : j ≤ J.jobs) :
    offset y0 j ≤ offset y0 J.jobs := offset_le h hj le_rfl

theorem acc_eq (h : EncodesInstance y0 J) {p : ℕ} (hp : p < y0.length) :
    (y0 ++ [W]).getD p 0 = y0.getD p 0 := getD_append_left hp

theorem jobCount_eq (h : EncodesInstance y0 J) : jobCount (y0 ++ [W]) = J.jobs := by
  unfold jobCount; rw [acc_eq h (by rw [len_eq h]; omega)]; exact h.jobCount_eq

theorem machineCount_eq (h : EncodesInstance y0 J) : machineCount (y0 ++ [W]) = J.machines := by
  unfold machineCount; rw [acc_eq h (by rw [len_eq h]; omega)]; exact h.machineCount_eq

theorem proc_eq (h : EncodesInstance y0 J) (j : Fin J.jobs) : proc (y0 ++ [W]) j = J.p j := by
  unfold proc; rw [acc_eq h (by rw [len_eq h]; omega)]; exact h.proc_eq j

theorem due_eq (h : EncodesInstance y0 J) (j : Fin J.jobs) : due (y0 ++ [W]) j = J.d j := by
  unfold due; rw [jobCount_eq h, acc_eq h (by rw [len_eq h]; omega)]
  have := h.due_eq j; unfold due at this; rwa [h.jobCount_eq] at this

theorem wt_eq (h : EncodesInstance y0 J) (j : Fin J.jobs) : wt (y0 ++ [W]) j = J.w j := by
  unfold wt; rw [jobCount_eq h, acc_eq h (by rw [len_eq h]; omega)]
  have := h.wt_eq j; unfold wt at this; rwa [h.jobCount_eq] at this

theorem offset_eq (h : EncodesInstance y0 J) {i : ℕ} (hi : i ≤ J.jobs) :
    offset (y0 ++ [W]) i = offset y0 i := by
  unfold offset; rw [jobCount_eq h, acc_eq h (by rw [len_eq h]; omega)]
  rw [h.jobCount_eq]

theorem target_eq (h : EncodesInstance y0 J) {t : ℕ} (ht : t < offset y0 J.jobs) :
    target (y0 ++ [W]) t = target y0 t := by
  unfold target; rw [jobCount_eq h, acc_eq h (by rw [len_eq h]; omega)]
  rw [h.jobCount_eq]

theorem lastOf_eq : lastOf (y0 ++ [W]) = W := by
  unfold lastOf
  rw [List.getD_eq_getElem?_getD]
  simp

theorem inBlock_iff (h : EncodesInstance y0 J) (j : Fin J.jobs) (i : Fin J.machines) :
    inBlock (y0 ++ [W]) j i = true ↔ i ∈ J.eligible j := by
  rw [h.eligible_iff]
  have hj1 := offset_le_last h (j := j.val + 1) j.isLt
  have hL : offset y0 J.jobs < (y0 ++ [W]).length := by
    rw [List.length_append, len_eq h]; simp only [List.length_singleton]; omega
  unfold inBlock
  rw [offset_eq h (Nat.le_of_lt_succ (Nat.lt_succ_of_lt j.isLt)), offset_eq h j.isLt]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    have htT : t < offset y0 (j + 1) := lt_of_lt_of_le ht (min_le_left _ _)
    exact ⟨t, h1, htT, (target_eq h (lt_of_lt_of_le htT hj1)).symm.trans h2⟩
  · rintro ⟨t, h1, h2, h3⟩
    exact ⟨t, lt_min h2 (by omega), h1, (target_eq h (lt_of_lt_of_le h2 hj1)).trans h3⟩

theorem machListW_eq (h : EncodesInstance y0 J) (j : Fin J.jobs) :
    machListW (y0 ++ [W]) J.machines j = machList J j := by
  unfold machListW machList
  congr 1
  refine List.filter_congr fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [dif_pos hi']
  exact Bool.eq_iff_iff.mpr ((inBlock_iff h j ⟨i, hi'⟩).trans (decide_eq_true_iff).symm)

theorem listSum_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem totalW_eq (h : EncodesInstance y0 J) :
    totalW (y0 ++ [W]) J.jobs = totalWeight J := by
  unfold totalW totalWeight
  rw [listSum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => wt_eq h j

theorem ofFn_eq_range {n : ℕ} (g : Fin n → List ℕ) :
    (List.ofFn g).flatten = (List.range n).flatMap fun j => if h : j < n then g ⟨j, h⟩ else [] := by
  rw [← Lax434175Proofs.ThresholdProgram.ofFn_flatten]
  congr 2
  funext j
  rw [dif_pos j.isLt]

theorem diffWord_eq (S W : ℕ) :
    diffWord S W = [if (S : ℤ) - W < 0 then 1 else 0, ((S : ℤ) - W).natAbs] := by
  unfold diffWord
  by_cases h : S < W
  · rw [if_pos h, if_pos h, if_pos (by omega)]; congr 2; omega
  · rw [if_neg h, if_neg h, if_neg (by omega)]; congr 2; omega

/-- **The map writes the standard word** on the words of instances whose machines
are at most the length of the word. -/
theorem stdOfWord_eq (h : EncodesInstance y0 J) (hm : J.machines ≤ (y0 ++ [W]).length) :
    stdOfWord (y0 ++ [W]) = stdWord J W := by
  have hL : (y0 ++ [W]).length = 4 + 4 * J.jobs + offset y0 J.jobs := by
    rw [List.length_append, len_eq h]; simp only [List.length_singleton]; omega
  have hn : capN (y0 ++ [W]) = J.jobs := by
    unfold capN; rw [jobCount_eq h]; omega
  have hmm : capM (y0 ++ [W]) = J.machines := by
    unfold capM; rw [machineCount_eq h]; omega
  have hrows : (List.range J.jobs).flatMap (fun j => (recW (y0 ++ [W]) J.machines j).length ::
      recW (y0 ++ [W]) J.machines j) =
      (List.range J.jobs).flatMap fun j => if h : j < J.jobs then (rec J ⟨j, h⟩).length :: rec J ⟨j, h⟩ else [] := by
    refine List.flatMap_congr fun j hj => ?_
    have hj' := List.mem_range.mp hj
    rw [dif_pos hj']
    have hr : recW (y0 ++ [W]) J.machines j = rec J ⟨j, hj'⟩ := by
      unfold recW rec
      rw [proc_eq h ⟨j, hj'⟩, machListW_eq h ⟨j, hj'⟩]
    rw [hr]
  have hobj : (List.range J.jobs).flatMap (fun j => [0, wt (y0 ++ [W]) j, due (y0 ++ [W]) j]) =
      (List.range J.jobs).flatMap fun j => if h : j < J.jobs then [0, J.w ⟨j, h⟩, J.d ⟨j, h⟩] else [] := by
    refine List.flatMap_congr fun j hj => ?_
    have hj' := List.mem_range.mp hj
    rw [dif_pos hj', wt_eq h ⟨j, hj'⟩, due_eq h ⟨j, hj'⟩]
  unfold stdOfWord stdWord stdInst
  rw [hn, hmm, lastOf_eq, totalW_eq h, diffWord_eq, ofFn_eq_range, ofFn_eq_range, hrows, hobj]

-- Dropping unused machines on words

/-- Position `q` holds the first occurrence of its value. -/
def firstB (f : ℕ → ℕ) (q : ℕ) : Bool := (List.range q).all fun q' => f q' != f q

/-- The positions below `T` of first occurrences. -/
def firsts (f : ℕ → ℕ) (T : ℕ) : List ℕ := (List.range T).filter (firstB f)

/-- The number of distinct values below `T` less than `v`. -/
def rankW (f : ℕ → ℕ) (T v : ℕ) : ℕ := ((firsts f T).filter fun q => decide (f q < v)).length

/-- **Counting distinct values by first occurrences.** -/
theorem firsts_count (f : ℕ → ℕ) (P : ℕ → Bool) (T : ℕ) :
    ((firsts f T).filter fun q => P (f q)).length = (((Finset.range T).image f).filter fun v => P v).card := by
  induction T with
  | zero => simp [firsts]
  | succ T ih =>
    unfold firsts at ih ⊢
    rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, ih,
      Finset.range_add_one, Finset.image_insert]
    by_cases hf : firstB f T = true
    · have hnot : f T ∉ (Finset.range T).image f := by
        intro hm
        obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hm
        have := List.all_eq_true.mp hf q (List.mem_range.mpr (Finset.mem_range.mp hq))
        simp [he] at this
      rw [Finset.filter_insert]
      by_cases hP : P (f T) = true
      · rw [if_pos hP, Finset.card_insert_of_notMem (fun h => hnot (Finset.mem_filter.mp h).1)]
        simp [hf, hP]
      · rw [if_neg hP]
        simp [hf, hP]
    · have hin : f T ∈ (Finset.range T).image f := by
        simp only [firstB, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq, not_forall,
          not_not] at hf
        obtain ⟨q, hq, he⟩ := hf
        exact Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr hq, he⟩
      rw [Finset.insert_eq_of_mem hin]
      simp [hf]

/-- The word with the unused machines dropped and the others renumbered. -/
def compressWord (x : List ℕ) : List ℕ :=
  let n := capN x
  let T := min (offset x n) x.length
  [n, (firsts (target x) T).length] ++ (List.range (4 * n + 1)).map (fun p => x.getD (2 + p) 0) ++
    (List.range T).map (fun q => rankW (target x) T (target x q)) ++ [lastOf x]

section Compress
open Lax434175Proofs.IsemCompress

variable {y0 : List ℕ} {I : Instance} {W : ℕ}

/-- Every position of the target array lies in the block of some job. -/
theorem cover (h : EncodesInstance y0 I) {q : ℕ} (hq : q < offset y0 I.jobs) :
    ∃ j < I.jobs, offset y0 j ≤ q ∧ q < offset y0 (j + 1) := by
  classical
  have hex : ∃ j, q < offset y0 (j + 1) ∧ j < I.jobs := by
    rcases Nat.eq_zero_or_pos I.jobs with h0 | h0
    · rw [h0, h.offset_zero] at hq; omega
    · exact ⟨I.jobs - 1, by rwa [Nat.sub_add_cancel h0], by omega⟩
  let j := Nat.find hex
  have hj : q < offset y0 (j + 1) ∧ j < I.jobs := Nat.find_spec hex
  refine ⟨j, hj.2, ?_, hj.1⟩
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · rw [h0, h.offset_zero]; omega
  · have := Nat.find_min hex (show j - 1 < j by omega)
    rw [Nat.sub_add_cancel h0] at this
    by_contra hlt
    exact this ⟨by omega, by omega⟩

/-- The values of the target array are the used machines. -/
theorem image_target (h : EncodesInstance y0 I) :
    (Finset.range (offset y0 I.jobs)).image (target y0) = (used I).image Fin.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨j, hj, h1, h2⟩ := cover h hq
    let i : Fin I.machines := ⟨target y0 q, h.target_lt q hq⟩
    have hi : i ∈ I.eligible ⟨j, hj⟩ := (h.eligible_iff ⟨j, hj⟩ i).mpr ⟨q, h1, h2, rfl⟩
    exact ⟨i, mem_used hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, -, hij⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨t, h1, h2, h3⟩ := (h.eligible_iff j i).mp hij
    exact ⟨t, lt_of_lt_of_le h2 (offset_le h (show j.val + 1 ≤ I.jobs from j.isLt) le_rfl), h3⟩

theorem count_used (h : EncodesInstance y0 I) :
    (firsts (target y0) (offset y0 I.jobs)).length = (used I).card := by
  have := firsts_count (target y0) (fun _ => true) (offset y0 I.jobs)
  simp only [List.filter_true] at this
  rw [this, image_target h]
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial)]
  exact Finset.card_image_of_injective _ Fin.val_injective

theorem rankW_eq (h : EncodesInstance y0 I) (i : Fin I.machines) :
    rankW (target y0) (offset y0 I.jobs) i.val = rank I i := by
  unfold rankW rank
  rw [firsts_count (target y0) (fun v => decide (v < i.val)), image_target h, Finset.filter_image,
    Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext u
  simp only [Finset.mem_filter, decide_eq_true_eq]
  exact and_congr_right fun _ => Fin.lt_def.symm


theorem firsts_congr {f g : ℕ → ℕ} {T : ℕ} (hfg : ∀ q < T, f q = g q) : firsts f T = firsts g T := by
  unfold firsts
  refine List.filter_congr fun q hq => ?_
  have hq' := List.mem_range.mp hq
  unfold firstB
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  rw [hfg q hq']
  exact forall_congr' fun q' => imp_congr_right fun h2 => by rw [hfg q' (lt_trans h2 hq')]

theorem rankW_congr {f g : ℕ → ℕ} {T : ℕ} (hfg : ∀ q < T, f q = g q) (v : ℕ) :
    rankW f T v = rankW g T v := by
  unfold rankW
  rw [firsts_congr hfg]
  congr 1
  refine List.filter_congr fun q hq => ?_
  have : q < T := List.mem_range.mp (List.mem_filter.mp hq).1
  rw [hfg q this]

theorem getD_three (a b c : List ℕ) (k : ℕ) : (a ++ b ++ c).getD k 0 =
    if k < a.length then a.getD k 0 else if k - a.length < b.length then b.getD (k - a.length) 0
    else c.getD (k - a.length - b.length) 0 := by
  rw [List.append_assoc]
  by_cases h1 : k < a.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1, List.getD_append_right _ _ _ _ (by omega)]
    by_cases h2 : k - a.length < b.length
    · rw [if_pos h2, List.getD_append _ _ _ _ h2]
    · rw [if_neg h2, List.getD_append_right _ _ _ _ (by omega)]

theorem getD_map_range {g : ℕ → ℕ} {k n : ℕ} (hk : k < n) : ((List.range n).map g).getD k 0 = g k := by
  rw [List.getD_eq_getElem?_getD]; simp [hk]

/-- **Dropping the unused machines on words.** -/
theorem compressWord_eq (h : EncodesInstance y0 I) :
    ∃ y1, compressWord (y0 ++ [W]) = y1 ++ [W] ∧ EncodesInstance y1 (compress I) ∧
      (compress I).machines ≤ y1.length := by
  set x := y0 ++ [W] with hx
  set n := I.jobs
  set T := offset y0 I.jobs with hT
  have hL : x.length = 4 + 4 * n + T := by
    rw [hx, List.length_append, len_eq h]; simp only [List.length_singleton]; omega
  have hn : capN x = n := by unfold capN; rw [jobCount_eq h]; omega
  have hTx : min (offset x (capN x)) x.length = T := by
    rw [hn, offset_eq h le_rfl]; omega
  have hft : ∀ q < T, target x q = target y0 q := fun q hq => target_eq h hq
  set f := target y0
  set m' := (firsts f T).length with hm'
  let mid := (List.range (4 * n + 1)).map fun p => x.getD (2 + p) 0
  let tg := (List.range T).map fun q => rankW f T (f q)
  refine ⟨[n, m'] ++ mid ++ tg, ?_, ?_, ?_⟩
  · have hmap : (List.range T).map (fun q => rankW (target x) T (target x q)) = tg :=
      List.map_congr_left fun q hq => by
        rw [rankW_congr hft, hft q (List.mem_range.mp hq)]
    unfold compressWord
    simp only []
    rw [hTx, hn, lastOf_eq, firsts_congr hft, hmap]
  · set y1 := [n, m'] ++ mid ++ tg with hy1
    have hmid_len : mid.length = 4 * n + 1 := by simp [mid]
    have g0 : y1.getD 0 0 = n := rfl
    have g1 : y1.getD 1 0 = m' := rfl
    have gmid : ∀ p < 4 * n + 1, y1.getD (2 + p) 0 = x.getD (2 + p) 0 := by
      intro p hp
      rw [hy1, getD_three, if_neg (by simp; omega), if_pos (by simp [hmid_len]; omega)]
      simp only [List.length_cons, List.length_nil]
      rw [show 2 + p - (0 + 1 + 1) = p by omega]
      exact getD_map_range hp
    have gtg : ∀ t < T, y1.getD (3 + 4 * n + t) 0 = rankW f T (f t) := by
      intro t ht
      rw [hy1, getD_three, if_neg (by simp; omega), if_neg (by simp [hmid_len]; omega)]
      simp only [List.length_cons, List.length_nil, hmid_len]
      rw [show 3 + 4 * n + t - (0 + 1 + 1) - (4 * n + 1) = t by omega]
      exact getD_map_range ht
    have hjc : jobCount y1 = n := g0
    have hcj : (compress I).jobs = n := rfl
    have hoff : ∀ i ≤ n, offset y1 i = offset y0 i := by
      intro i hi
      unfold offset
      rw [hjc, show 2 + 3 * n + i = 2 + (3 * n + i) by omega, gmid _ (by omega),
        show 2 + (3 * n + i) = 2 + 3 * jobCount x + i by rw [jobCount_eq h]; omega]
      exact offset_eq h hi
    have htgt : ∀ t < T, target y1 t = rankW f T (f t) := by
      intro t ht
      unfold target; rw [hjc]; exact gtg t ht
    have hrank : ∀ t (ht : t < T), rankW f T (f t) = rank I ⟨f t, h.target_lt t ht⟩ :=
      fun t ht => rankW_eq h ⟨f t, h.target_lt t ht⟩
    refine ⟨hjc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show m' = (used I).card
      exact count_used h
    · show y1.length = 3 + 4 * n + offset y1 n
      have hT' : offset y0 n = T := rfl
      rw [hoff n le_rfl, hT', hy1]
      simp only [List.length_append, List.length_cons, List.length_nil, hmid_len, tg, List.length_map,
        List.length_range]
      omega
    · intro j
      unfold proc
      rw [gmid _ (by omega)]
      exact proc_eq h j
    · intro j
      unfold due
      rw [hjc, show 2 + n + j = 2 + (n + j) by omega, gmid _ (by omega),
        show 2 + (n + j.val) = 2 + jobCount x + j by rw [jobCount_eq h]; omega]
      exact due_eq h j
    · intro j
      unfold wt
      rw [hjc, show 2 + 2 * n + j = 2 + (2 * n + j) by omega, gmid _ (by omega),
        show 2 + (2 * n + j.val) = 2 + 2 * jobCount x + j by rw [jobCount_eq h]; omega]
      exact wt_eq h j
    · rw [hoff 0 (Nat.zero_le _)]; exact h.offset_zero
    · intro j hj
      rw [hoff j hj.le, hoff (j + 1) hj]
      exact h.offset_mono j hj
    · intro t ht
      change t < offset y1 n at ht
      rw [hoff n le_rfl] at ht
      rw [htgt t ht, hrank t ht]
      obtain ⟨j, hj, h1, h2⟩ := cover h ht
      have hi : (⟨f t, h.target_lt t ht⟩ : Fin I.machines) ∈ I.eligible ⟨j, hj⟩ :=
        (h.eligible_iff ⟨j, hj⟩ _).mpr ⟨t, h1, h2, rfl⟩
      exact rank_lt (mem_used hi)
    · intro j r
      have hj1 : j.val + 1 ≤ n := j.isLt
      have hfit : ∀ t, t < offset y0 (j.val + 1) → t < T :=
        fun t ht => lt_of_lt_of_le ht (offset_le_last h hj1)
      refine (mem_compress (I := I) (j := j) (r := r)).trans ?_
      rw [hoff j (by omega), hoff (j.val + 1) hj1]
      constructor
      · rintro ⟨i, hi, hr⟩
        obtain ⟨t, h1, h2, h3⟩ := (h.eligible_iff j i).mp hi
        refine ⟨t, h1, h2, ?_⟩
        rw [htgt t (hfit t h2), hrank t (hfit t h2)]
        have he : (⟨f t, h.target_lt t (hfit t h2)⟩ : Fin I.machines) = i := Fin.ext h3
        rw [he, hr]
      · rintro ⟨t, h1, h2, h3⟩
        rw [htgt t (hfit t h2), hrank t (hfit t h2)] at h3
        exact ⟨_, (h.eligible_iff j _).mpr ⟨t, h1, h2, rfl⟩, h3⟩

  · show (used I).card ≤ ([n, m'] ++ mid ++ tg).length
    rw [show (used I).card = m' from (count_used h).symm]
    have h1 : m' ≤ T := by
      show (firsts f T).length ≤ T
      unfold firsts; exact (List.length_filter_le _ _).trans (by simp)
    simp only [List.length_append, List.length_cons, List.length_nil, tg, List.length_map,
      List.length_range]
    omega

end Compress

end Lax434175Proofs.IsemWords
