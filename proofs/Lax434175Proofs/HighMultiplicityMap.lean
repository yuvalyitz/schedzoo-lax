import Mathlib.Tactic
import Lax434175Proofs.P200ProgramsSpec
import Lax434175Proofs.ThresholdProgram

/-!
The word map from standard words to high-multiplicity words, as a function on all words.

A standard word is `[0, n, m]`, the records of the jobs, each preceded by its length, the
block of facts on pairs, the block of global facts, the release date, weight and due date of
every job, and the threshold. The *tuple* of job `j` is its record followed by its three
numbers. `hmWord` writes `[1, n, m]`, the number of distinct tuples, then every distinct tuple
once, preceded by its length and by the number of jobs that have it, in increasing order of
these extended tuples, then copies the two blocks and the threshold.

The order is found by ranks: a job is *first* if no earlier job has its tuple, and its rank is
the number of first jobs with a smaller extended tuple; the tuples of rank `0, 1, …` are
written in turn. Tuples are compared entry by entry, `cmpL` (`0` for equal lists, `1` for a
smaller first list, `2` for a larger one), which a scan of both lists computes (`cmpUp`).

Every count is capped by the length of the word, so the map is polynomial on every word; on
the words of instances the caps change nothing.
-/

namespace Lax434175Proofs.HighMultiplicityMap
open Lax434175Proofs.P200Programs (nA posA)
open Lax434175Proofs.ThresholdProgram (indN indN_zero indN_pos indN_le)

/-! ### Comparing two lists -/

/-- `0` for equal lists, `1` when the first is smaller, `2` when it is larger. -/
def cmpL : List ℕ → List ℕ → ℕ
  | [], [] => 0
  | [], _ :: _ => 1
  | _ :: _, [] => 2
  | a :: l, b :: l' => if a < b then 1 else if b < a then 2 else cmpL l l'

theorem cmpL_le_two : ∀ l l' : List ℕ, cmpL l l' ≤ 2
  | [], [] => by simp [cmpL]
  | [], _ :: _ => by simp [cmpL]
  | _ :: _, [] => by simp [cmpL]
  | a :: l, b :: l' => by
    simp only [cmpL]; split_ifs
    · omega
    · omega
    · exact cmpL_le_two l l'

theorem cmpL_eq_zero : ∀ l l' : List ℕ, cmpL l l' = 0 ↔ l = l'
  | [], [] => by simp [cmpL]
  | [], _ :: _ => by simp [cmpL]
  | _ :: _, [] => by simp [cmpL]
  | a :: l, b :: l' => by
    simp only [cmpL, List.cons.injEq]
    split_ifs with h1 h2
    · simp only [false_iff, not_and]; intro h; omega
    · simp only [false_iff, not_and]; intro h; omega
    · rw [cmpL_eq_zero l l']; constructor
      · intro h; exact ⟨by omega, h⟩
      · intro h; exact h.2

theorem cmpL_eq_one : ∀ l l' : List ℕ, cmpL l l' = 1 ↔ l < l'
  | [], [] => by simp [cmpL]
  | [], _ :: _ => by simp [cmpL, List.nil_lt_cons]
  | _ :: _, [] => by simp [cmpL, List.not_lt_nil]
  | a :: l, b :: l' => by
    simp only [cmpL, List.cons_lt_cons_iff]
    split_ifs with h1 h2
    · simp [h1]
    · simp only [OfNat.ofNat_ne_one, false_iff, not_or, not_and]; exact ⟨by omega, by omega⟩
    · rw [cmpL_eq_one l l']; constructor
      · intro h; exact Or.inr ⟨by omega, h⟩
      · rintro (h | ⟨-, h⟩)
        · omega
        · exact h

/-- The comparison at position `k`, in a scan of both lists. -/
def locC (l l' : List ℕ) (k : ℕ) : ℕ :=
  if k < l.length then
    if k < l'.length then
      (if l.getD k 0 < l'.getD k 0 then 1 else if l'.getD k 0 < l.getD k 0 then 2 else 0)
    else 2
  else if k < l'.length then 1 else 0

/-- The comparison after scanning `k` positions. -/
def cmpUp (l l' : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if cmpUp l l' k = 0 then locC l l' k else cmpUp l l' k

theorem locC_cons (a b : ℕ) (l l' : List ℕ) (k : ℕ) :
    locC (a :: l) (b :: l') (k + 1) = locC l l' k := by
  simp [locC]

theorem cmpUp_cons (a b : ℕ) (l l' : List ℕ) : ∀ k,
    cmpUp (a :: l) (b :: l') (k + 1) = if a < b then 1 else if b < a then 2 else cmpUp l l' k
  | 0 => by simp [cmpUp, locC]
  | k + 1 => by
    rw [cmpUp, cmpUp_cons a b l l' k, locC_cons]
    by_cases h1 : a < b
    · simp [h1]
    · by_cases h2 : b < a
      · simp [h1, h2]
      · simp only [h1, h2, if_false]; rfl

theorem cmpUp_nil : ∀ k, cmpUp [] [] k = 0
  | 0 => rfl
  | k + 1 => by rw [cmpUp, cmpUp_nil k]; simp [locC]

theorem cmpUp_of_first {l l' : List ℕ} (h : locC l l' 0 ≠ 0) : ∀ k, cmpUp l l' (k + 1) = locC l l' 0
  | 0 => by simp [cmpUp]
  | k + 1 => by rw [cmpUp, cmpUp_of_first h k, if_neg h]

/-- **The scan computes the comparison.** -/
theorem cmpUp_eq : ∀ (l l' : List ℕ) (k : ℕ), l.length ≤ k → l'.length ≤ k → cmpUp l l' k = cmpL l l'
  | [], [], k, _, _ => cmpUp_nil k
  | [], b :: l', k, _, h => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at h; omega⟩
    rw [cmpUp_of_first (by simp [locC])]; simp [locC, cmpL]
  | a :: l, [], k, h, _ => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at h; omega⟩
    rw [cmpUp_of_first (by simp [locC])]; simp [locC, cmpL]
  | a :: l, b :: l', k, h, h' => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at h; omega⟩
    rw [cmpUp_cons, cmpL, cmpUp_eq l l' k (by simp at h; omega) (by simp at h'; omega)]

/-! ### The arithmetic the program does -/

/-- `1` when the numbers are equal, `0` otherwise. -/
def eqN (a b : ℕ) : ℕ := 1 - ((a - b) + (b - a))

theorem eqN_eq (a b : ℕ) : eqN a b = if a = b then 1 else 0 := by
  unfold eqN; split_ifs <;> omega

theorem indN_sub (a b : ℕ) : indN (a - b) = if b < a then 1 else 0 := by
  unfold indN; split_ifs <;> omega

/-- The comparison at one position from the two flags `f`, `g` (the position is inside the first,
the second list) and the two entries `a`, `b`. -/
def locN (f g a b : ℕ) : ℕ :=
  f * g * (indN (b - a) + 2 * indN (a - b)) + f * (1 - g) * 2 + (1 - f) * g

theorem locN_eq (l l' : List ℕ) (k : ℕ) {a b : ℕ} (ha : k < l.length → a = l.getD k 0)
    (hb : k < l'.length → b = l'.getD k 0) :
    locN (indN (l.length - k)) (indN (l'.length - k)) a b = locC l l' k := by
  unfold locN locC
  rw [indN_sub, indN_sub]
  by_cases h1 : k < l.length <;> by_cases h2 : k < l'.length
  · rw [← ha h1, ← hb h2, indN_sub, indN_sub]; simp only [h1, h2, if_true]
    by_cases h3 : a < b
    · simp [h3, show ¬ b < a by omega]
    · by_cases h4 : b < a <;> simp [h3, h4]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- The new state of the scan. -/
theorem step_eq (st w : ℕ) : st + (1 - indN st) * w = if st = 0 then w else st := by
  unfold indN; split_ifs <;> simp_all; omega

/-- Where entry `k` of a tuple is, from the flag `h` (inside the record). -/
theorem idx_eq (N P O k : ℕ) :
    indN (N - k) * (P + k) + (1 - indN (N - k)) * (O + k - N) =
      if k < N then P + k else O + (k - N) := by
  rw [indN_sub]; split_ifs <;> omega

/-! ### The word map -/

section Map
variable (u : List ℕ)

/-- The length of the record of job `j`, capped by the length of the word. -/
def lnH (j : ℕ) : ℕ := min (u.getD (posA u j) 0) u.length

/-- Where the release dates, weights and due dates begin. -/
def obH : ℕ := u.length - 2 - 3 * nA u

/-- Where entry `k` of the tuple of job `j` is: its record, then its three numbers. -/
def idxH (j k : ℕ) : ℕ := if k < lnH u j then posA u j + 1 + k else obH u + 3 * j + (k - lnH u j)

/-- The tuple of job `j`: its record, then its release date, weight and due date. -/
def tupH (j : ℕ) : List ℕ := (List.range (lnH u j + 3)).map fun k => u.getD (idxH u j k) 0

/-- The number of jobs with the tuple of job `j`. -/
def cntH (j : ℕ) : ℕ := ((List.range (nA u)).filter fun i => cmpL (tupH u i) (tupH u j) == 0).length

/-- No earlier job has the tuple of job `j`. -/
def fstH (j : ℕ) : Bool :=
  !((List.range (nA u)).any fun i => decide (i < j) && cmpL (tupH u i) (tupH u j) == 0)

/-- The tuple of job `i`, its number in front, is smaller than that of job `j`. -/
def lessH (i j : ℕ) : Bool :=
  decide (cntH u i < cntH u j) || (cntH u i == cntH u j && cmpL (tupH u i) (tupH u j) == 1)

/-- The rank of job `j`: the first jobs with a smaller tuple. -/
def rkH (j : ℕ) : ℕ := ((List.range (nA u)).filter fun i => fstH u i && lessH u i j).length

/-- The number of distinct tuples. -/
def ddH : ℕ := ((List.range (nA u)).filter (fstH u)).length

/-- The tuple of job `j` with its number and its length in front, if `j` is first with rank `r`. -/
def outH (r j : ℕ) : List ℕ :=
  if fstH u j && rkH u j == r then (lnH u j + 4) :: cntH u j :: tupH u j else []

/-- The block of facts on pairs and the block of global facts. -/
def midH : List ℕ :=
  (List.range (obH u - posA u (nA u))).map fun k => u.getD (posA u (nA u) + k) 0

end Map

/-- **The word map.** -/
def hmWord (u : List ℕ) : List ℕ :=
  [1, u.getD 1 0, u.getD 2 0, ddH u] ++
    (List.range (nA u)).flatMap (fun r => (List.range (nA u)).flatMap (outH u r)) ++ midH u ++
    [u.getD (u.length - 2) 0, u.getD (u.length - 1) 0]

theorem tupH_length (u : List ℕ) (j : ℕ) : (tupH u j).length = lnH u j + 3 := by simp [tupH]

theorem tupH_getD (u : List ℕ) (j : ℕ) {k : ℕ} (hk : k < (tupH u j).length) :
    (tupH u j).getD k 0 = u.getD (idxH u j k) 0 := by
  rw [tupH_length] at hk
  simp [tupH, List.getD_eq_getElem?_getD, hk]

end Lax434175Proofs.HighMultiplicityMap
