import Mathlib.Tactic
import Lax434175.Sanity
import Lax808846Proofs.Spec
import Lax434175Proofs.Cost.Glue
import Lax434175Proofs.IsemPrograms
import Lax434175Proofs.PreemptionUseless
import Lax434175Proofs.P200Words

/-!
Smith's rule end to end: `1||ΣwjCj` (`Sanity.singleWC`) is decided within `O(n log n)`
instructions of the word RAM plus the length of the word, on short words (`smith`).

* **Semantics** (`decides_iff`). On one machine the jobs run without idle time in Smith's order
  (`p_i w_j ≤ p_j w_i` puts `i` first, jobs of weight `0` last, ties by number) pay
  `opt = Σ w_j p_j + Σ_{i<j} min (p_i w_j, p_j w_i)`, and every feasible schedule pays at least
  that: the jobs that complete before a job fill the machine up to its completion
  (`PreemptionUseless.capacity`), and every order pays at least the smaller term of every pair
  (`pairs_ge`).
* **Words** (`word_eq`). The standard word of an instance is `stdInst n p w` followed by the
  threshold: a record of fifteen numbers per job, the empty block of pairs, the block of global
  facts, and a triple `[0, w_j, 0]` per job.
* **Merge sort** (`run_msort`), written for any keys and any comparison command of constant
  cost (`Cmp`): bottom-up, `⌈log₂ n⌉` passes of linear cost, `sortCost Kc n` in all.
* **The program** (`run_smith`): the word read into memory, the times and weights copied into
  two arrays, the jobs sorted by Smith's comparison (`cmpSmith`), the weighted completion times
  added up and compared with the threshold; the sorted order costs `opt` (`seqCost_eq_opt`).
* **Glue** (`smith`): `Cost.decidesWithin_of_solves` with values below `64 (|u| + M + 2)^4`.
-/

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

namespace Lax434175Proofs.Smith

/-! ### Segments of a function -/

/-- The entries `f a, …, f (b - 1)`. -/
def seg (f : ℕ → ℕ) (a b : ℕ) : List ℕ := (List.range (b - a)).map fun t => f (a + t)

@[simp] theorem length_seg (f : ℕ → ℕ) (a b : ℕ) : (seg f a b).length = b - a := by simp [seg]

theorem getElem_seg (f : ℕ → ℕ) (a b t : ℕ) (h : t < (seg f a b).length) :
    (seg f a b)[t] = f (a + t) := by simp [seg]

theorem seg_drop (f : ℕ → ℕ) (a b w : ℕ) : (seg f a b).drop w = seg f (a + w) b := by
  refine List.ext_getElem (by simp; omega) fun t h1 h2 => ?_
  simp only [List.getElem_drop, getElem_seg]
  congr 1; omega

theorem seg_take (f : ℕ → ℕ) (a b w : ℕ) : (seg f a b).take w = seg f a (min (a + w) b) := by
  refine List.ext_getElem (by simp; omega) fun t h1 h2 => ?_
  simp only [List.getElem_take, getElem_seg]

theorem seg_cons (f : ℕ → ℕ) {a b : ℕ} (h : a < b) : seg f a b = f a :: seg f (a + 1) b := by
  refine List.ext_getElem (by simp; omega) fun t h1 h2 => ?_
  rcases t with _ | t
  · simp [getElem_seg]
  · simp only [List.getElem_cons_succ, getElem_seg]
    congr 1; omega

theorem seg_empty (f : ℕ → ℕ) {a b : ℕ} (h : b ≤ a) : seg f a b = [] := by
  simp [seg, Nat.sub_eq_zero_of_le h]

/-! ### Bottom-up merge sort on lists -/

section MergeSort
variable (le : ℕ → ℕ → Bool)

/-- One pass of bottom-up merge sort of width `w`: consecutive blocks of `w` entries are
merged in pairs. -/
def passL (w : ℕ) (l : List ℕ) : List ℕ :=
  if _h : w = 0 ∨ l = [] then l
  else List.merge (l.take w) ((l.drop w).take w) le ++ passL w (l.drop (2 * w))
termination_by l.length
decreasing_by
  simp only [not_or] at _h
  rw [List.length_drop]
  have : 0 < l.length := List.length_pos_iff.mpr _h.2
  omega

@[simp] theorem passL_nil (w : ℕ) : passL le w [] = [] := by
  rw [passL]; simp

theorem passL_cons {w : ℕ} {l : List ℕ} (hw : 0 < w) (hl : l ≠ []) :
    passL le w l = List.merge (l.take w) ((l.drop w).take w) le ++ passL le w (l.drop (2 * w)) := by
  rw [passL, dif_neg (by rintro (h | h) <;> [omega; exact hl h])]

theorem drop_two_mul (l : List ℕ) (w : ℕ) : l.drop (2 * w) = (l.drop w).drop w := by
  rw [List.drop_drop]; congr 1; omega

/-- A pass permutes its list. -/
theorem passL_perm (w : ℕ) : ∀ (k : ℕ) (l : List ℕ), l.length = k → (passL le w l).Perm l := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro l hk
  by_cases h : w = 0 ∨ l = []
  · rw [passL, dif_pos h]
  · simp only [not_or] at h
    rw [passL_cons le (Nat.pos_of_ne_zero h.1) h.2]
    have hlen : (l.drop (2 * w)).length < k := by
      rw [List.length_drop]
      have : 0 < l.length := List.length_pos_iff.mpr h.2
      omega
    have h1 := (List.merge_perm_append le (xs := l.take w) (ys := (l.drop w).take w)).append
      (ih _ hlen _ rfl)
    refine h1.trans ?_
    rw [drop_two_mul, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem length_passL (w : ℕ) (l : List ℕ) : (passL le w l).length = l.length :=
  (passL_perm le w _ l rfl).length_eq

/-- The relation of a comparison. -/
abbrev R (a b : ℕ) : Prop := le a b = true

/-- The blocks of width `w` are sorted. -/
def Chunks (w : ℕ) (l : List ℕ) : Prop := ∀ s, ((l.drop (s * w)).take w).Pairwise (R le)

theorem chunks_one (l : List ℕ) : Chunks le 1 l := by
  intro s
  rcases h : (l.drop (s * 1)).take 1 with _ | ⟨a, t⟩
  · exact List.Pairwise.nil
  · have := congrArg List.length h
    simp at this
    have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ht
    exact List.pairwise_singleton _ _

theorem sorted_of_chunks {w : ℕ} {l : List ℕ} (h : Chunks le w l) (hl : l.length ≤ w) :
    l.Pairwise (R le) := by
  have := h 0
  rwa [zero_mul, List.drop_zero, List.take_of_length_le hl] at this

variable {le}

/-- **A pass doubles the width of the sorted blocks.** -/
theorem chunks_passL (htr : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (htot : ∀ a b, (le a b || le b a) = true) {w : ℕ} (hw : 0 < w) :
    ∀ (k : ℕ) (l : List ℕ), l.length = k → Chunks le w l → Chunks le (2 * w) (passL le w l) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro l hk hc
  by_cases hl : l = []
  · subst hl; intro s; simp
  rw [passL_cons le hw hl]
  have hpos : 0 < l.length := List.length_pos_iff.mpr hl
  have hlen : (l.drop (2 * w)).length < k := by rw [List.length_drop]; omega
  have hX := hc 0
  have hY := hc 1
  rw [zero_mul, List.drop_zero] at hX
  rw [one_mul] at hY
  have hM : (List.merge (l.take w) ((l.drop w).take w) le).Pairwise (R le) :=
    List.pairwise_merge htr htot _ _ hX hY
  have hMlen : (List.merge (l.take w) ((l.drop w).take w) le).length =
      min (2 * w) l.length := by
    simp only [List.length_merge, List.length_take, List.length_drop]; omega
  have hrest : Chunks le w (l.drop (2 * w)) := by
    intro s
    have := hc (s + 2)
    rwa [List.drop_drop, show 2 * w + s * w = (s + 2) * w by ring]
  have IH := ih _ hlen _ rfl hrest
  intro s
  by_cases hbig : 2 * w ≤ l.length
  · rw [min_eq_left hbig] at hMlen
    rcases s with _ | s
    · rw [zero_mul, List.drop_zero, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
      exact hM
    · rw [List.drop_append, hMlen, List.drop_of_length_le (by nlinarith), List.nil_append,
        show (s + 1) * (2 * w) - 2 * w = s * (2 * w) by rw [Nat.succ_mul]; omega]
      exact IH s
  · have hnil : l.drop (2 * w) = [] := List.drop_of_length_le (by omega)
    rw [hnil, passL_nil, List.append_nil]
    rw [min_eq_right (by omega)] at hMlen
    rcases s with _ | s
    · rw [zero_mul, List.drop_zero, List.take_of_length_le (by omega)]
      exact hM
    · rw [List.drop_of_length_le (by rw [hMlen]; nlinarith)]
      simp

end MergeSort

/-! ### Pairs of jobs -/

section Pairs
variable {n : ℕ}

/-- A double sum over the ordered pairs is a sum over the pairs `i < j`. -/
theorem sum_pairs (h : Fin n → Fin n → ℕ) (hd : ∀ i, h i i = 0) :
    ∑ i, ∑ j, h i j = ∑ i, ∑ j, if i < j then h i j + h j i else 0 := by
  have e : ∀ i j, h i j = (if i < j then h i j else 0) + (if j < i then h i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, not_lt_of_gt hij]
    · simp [hd]
    · simp [hij, not_lt_of_gt hij]
  calc ∑ i, ∑ j, h i j
      = ∑ i, ∑ j, ((if i < j then h i j else 0) + (if j < i then h i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j
    _ = ∑ i, ∑ j, (if i < j then h i j else 0) + ∑ i, ∑ j, (if j < i then h i j else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = ∑ i, ∑ j, (if i < j then h i j else 0) + ∑ i, ∑ j, (if i < j then h j i else 0) := by
        rw [Finset.sum_comm (f := fun i j => if j < i then h i j else 0)]
    _ = ∑ i, ∑ j, if i < j then h i j + h j i else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp

variable (S : Fin n → Fin n → Prop) [DecidableRel S] (f : Fin n → Fin n → ℕ)

/-- **Every order of the jobs pays at least the smaller term of every pair.** -/
theorem pairs_ge (hirr : ∀ i, ¬ S i i) (htot : ∀ i j, i ≠ j → S i j ∨ S j i) :
    ∑ i, ∑ j, (if i < j then min (f i j) (f j i) else 0) ≤
      ∑ i, ∑ j, if S i j then f i j else 0 := by
  rw [sum_pairs (fun i j => if S i j then f i j else 0) (fun i => by simp [hirr])]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i < j
  · simp only [hij, if_true]
    rcases htot i j (ne_of_lt hij) with h | h
    · rw [if_pos h]; exact (min_le_left _ _).trans (Nat.le_add_right _ _)
    · rw [if_pos h (c := S j i)]; exact (min_le_right _ _).trans (Nat.le_add_left _ _)
  · simp [hij]

/-- **An order that puts the smaller term first everywhere pays exactly that.** -/
theorem pairs_eq (hirr : ∀ i, ¬ S i i) (htot : ∀ i j, i ≠ j → S i j ∨ S j i)
    (hasym : ∀ i j, S i j → ¬ S j i) (hle : ∀ i j, S i j → f i j ≤ f j i) :
    ∑ i, ∑ j, (if S i j then f i j else 0) =
      ∑ i, ∑ j, if i < j then min (f i j) (f j i) else 0 := by
  rw [sum_pairs (fun i j => if S i j then f i j else 0) (fun i => by simp [hirr])]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij h1 h2 h2
  · exact absurd h2 (hasym i j h1)
  · rw [add_zero, min_eq_left (hle i j h1)]
  · rw [zero_add, min_eq_right (hle j i h2)]
  · rcases htot i j (ne_of_lt hij) with h | h
    · exact absurd h h1
    · exact absurd h h2
  · rfl

end Pairs

/-! ### Smith's rule -/

section SmithRule
variable (p w : ℕ → ℕ)

/-- **Smith's comparison**: job `i` may go before job `j` when `p_i w_j ≤ p_j w_i`; jobs of
weight `0` go last. -/
def smithLe (i j : ℕ) : Bool := if w i = 0 then decide (w j = 0) else decide (p i * w j ≤ p j * w i)

theorem smithLe_trans (a b c : ℕ) (h1 : smithLe p w a b = true) (h2 : smithLe p w b c = true) :
    smithLe p w a c = true := by
  unfold smithLe at *
  by_cases ha : w a = 0
  · simp only [ha, if_true, decide_eq_true_eq] at h1 ⊢
    simp only [h1, if_true, decide_eq_true_eq] at h2
    exact h2
  · simp only [ha, if_false, decide_eq_true_eq] at h1 ⊢
    by_cases hb : w b = 0
    · simp only [hb, if_true, decide_eq_true_eq] at h2
      rw [h2]; simp
    · simp only [hb, if_false, decide_eq_true_eq] at h2
      have hb' : 0 < w b := Nat.pos_of_ne_zero hb
      have e1 : p a * w b * w c ≤ p b * w a * w c := Nat.mul_le_mul_right _ h1
      have e2 : p b * w c * w a ≤ p c * w b * w a := Nat.mul_le_mul_right _ h2
      have : w b * (p a * w c) ≤ w b * (p c * w a) := by
        calc w b * (p a * w c) = p a * w b * w c := by ring
          _ ≤ p b * w a * w c := e1
          _ = p b * w c * w a := by ring
          _ ≤ p c * w b * w a := e2
          _ = w b * (p c * w a) := by ring
      exact Nat.le_of_mul_le_mul_left this hb'

theorem smithLe_total (a b : ℕ) : (smithLe p w a b || smithLe p w b a) = true := by
  unfold smithLe
  by_cases ha : w a = 0 <;> by_cases hb : w b = 0 <;> simp [ha, hb]
  omega

theorem smithLe_mul {i j : ℕ} (h : smithLe p w i j = true) : p i * w j ≤ p j * w i := by
  unfold smithLe at h
  by_cases hi : w i = 0
  · simp only [hi, if_true, decide_eq_true_eq] at h
    rw [h, hi]; simp
  · simpa [hi] using h

/-- The least total weighted completion time on one machine: every job pays its own
processing time and, for every pair, the smaller of `p_i w_j` and `p_j w_i`. -/
def opt (n : ℕ) : ℕ :=
  ∑ j : Fin n, w j * p j + ∑ i : Fin n, ∑ j : Fin n, if i < j then min (p i * w j) (p j * w i) else 0

end SmithRule

/-! ### Merge sort in IMP+ -/

/-- The scalar `x` as an expression. -/
abbrev V (x : String) : Expr := .var x

/-- `x := x + 1` -/
abbrev incr (x : String) : Com := .assign x (.add (.var x) (.lit 1))

/-- One step of the merge of `A[i1..md)` and `A[i2..hi)`: the smaller head goes to `T[k]`. -/
def mstep (cmp : Com) : Com :=
  .seq (.ite (.lt (V "i1") (V "md"))
    (.ite (.lt (V "i2") (V "hi"))
      (.seq (.assign "x" (.get "A" (V "i1"))) (.seq (.assign "y" (.get "A" (V "i2"))) (.seq cmp
        (.ite (.eq (V "c") (.lit 1))
          (.seq (.store "T" (V "k") (V "x")) (incr "i1"))
          (.seq (.store "T" (V "k") (V "y")) (incr "i2"))))))
      (.seq (.store "T" (V "k") (.get "A" (V "i1"))) (incr "i1")))
    (.seq (.store "T" (V "k") (.get "A" (V "i2"))) (incr "i2")))
  (incr "k")

/-- The scalars the sort writes, besides those of the comparison. -/
def sortVars : List String := ["wd", "i", "md", "hi", "i1", "i2", "k", "x", "y"]

/-- What the sort asks of a comparison `cmp` of the keys `x` and `y`: it sets `c` to `1` when
`le x y` and to `0` otherwise, within `Kc`; it writes no array and none of the scalars of the
sort; the context it needs survives the sort; and `le` is a total preorder. -/
structure Cmp (B : ℕ) (cmp : Com) (le : ℕ → ℕ → Bool) (Ctx : Env → Prop) (Key : ℕ → Prop)
    (Kc : ℕ) : Prop where
  run : ∀ σ, Ctx σ → Key (σ.vars "x") → Key (σ.vars "y") →
    ∃ σ', Run B cmp σ σ' Kc ∧ σ'.vars "c" = if le (σ.vars "x") (σ.vars "y") then 1 else 0
  wvars : ∀ v ∈ cmp.wvars, v ∉ sortVars ∧ v ≠ "n"
  warrs : cmp.warrs = []
  ctx : ∀ σ σ', Ctx σ → (∀ v, v ∉ sortVars → v ∉ cmp.wvars → σ'.vars v = σ.vars v) →
    (∀ a, a ≠ "A" → a ≠ "T" → σ'.arrs a = σ.arrs a) → Ctx σ'
  trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  total : ∀ a b, (le a b || le b a) = true
  keyB : ∀ a, Key a → a < B

section MSort
variable {B N n Kc : ℕ} {cmp : Com} {le : ℕ → ℕ → Bool} {Ctx : Env → Prop} {Key : ℕ → Prop}

theorem Cmp.notMem (hc : Cmp B cmp le Ctx Key Kc) {v : String} (hv : v ∈ sortVars ∨ v = "n") :
    v ∉ cmp.wvars := by
  intro hm
  have := hc.wvars v hm
  rcases hv with hv | hv
  · exact this.1 hv
  · exact this.2 hv

theorem Cmp.step (hc : Cmp B cmp le Ctx Key Kc) {σ : Env} (hσ : Ctx σ)
    (hx : Key (σ.vars "x")) (hy : Key (σ.vars "y")) :
    ∃ σ', Run B cmp σ σ' Kc ∧ σ'.vars "c" = (if le (σ.vars "x") (σ.vars "y") then 1 else 0) ∧
      (∀ v, v ∈ sortVars ∨ v = "n" → σ'.vars v = σ.vars v) ∧ σ'.arrs = σ.arrs ∧ Ctx σ' := by
  obtain ⟨σ', hr, hcv⟩ := hc.run σ hσ hx hy
  refine ⟨σ', hr, hcv, fun v hv => hr.frame_var v (hc.notMem hv),
    hr.frame_arrs_eqOn hc.warrs, ?_⟩
  exact hc.ctx σ σ' hσ (fun v _ hv => hr.frame_var v hv)
    (fun a _ _ => by rw [hr.frame_arrs_eqOn hc.warrs])

theorem Cmp.ctx_setVar (hc : Cmp B cmp le Ctx Key Kc) {σ : Env} (hσ : Ctx σ) {v : String}
    (hv : v ∈ sortVars) (x : ℕ) : Ctx (σ.setVar v x) :=
  hc.ctx σ _ hσ (fun w hw _ => by
    simp only [vars_setVar]
    rw [if_neg (by rintro rfl; exact hw hv)]) (fun _ _ _ => rfl)

theorem Cmp.ctx_setArr (hc : Cmp B cmp le Ctx Key Kc) {σ : Env} (hσ : Ctx σ) {a : String}
    (ha : a = "A" ∨ a = "T") (i x : ℕ) : Ctx (σ.setArr a i x) :=
  hc.ctx σ _ hσ (fun _ _ _ => rfl) (fun b h1 h2 => by
    simp only [arrs_setArr]
    rw [if_neg (by rcases ha with rfl | rfl <;> assumption)])

/-- After a block of the list is consumed, the rest of the merge. -/
theorem drop_cons_eq {l r : List ℕ} {j a : ℕ} (h : l.drop j = a :: r) :
    l.getD j 0 = a ∧ l.drop (j + 1) = r := by
  constructor
  · have : (l.drop j)[0]? = some a := by rw [h]; rfl
    rw [List.getElem?_drop, Nat.add_zero] at this
    rw [List.getD_eq_getElem?_getD, this]; rfl
  · rw [← List.drop_drop, h]; rfl

/-- The state of the merge of `A[lo..md)` and `A[md..hi)` into `T`. -/
structure MInv (le : ℕ → ℕ → Bool) (Ctx : Env → Prop) (N n wd lo md hi : ℕ) (fA g0 : ℕ → ℕ)
    (σ : Env) : Prop where
  n_eq : σ.vars "n" = n
  wd_eq : σ.vars "wd" = wd
  i_eq : σ.vars "i" = lo
  md_eq : σ.vars "md" = md
  hi_eq : σ.vars "hi" = hi
  A_eq : σ.arrs "A" = arrOf N fA
  ctx : Ctx σ
  lo_i1 : lo ≤ σ.vars "i1"
  i1_md : σ.vars "i1" ≤ md
  md_i2 : md ≤ σ.vars "i2"
  i2_hi : σ.vars "i2" ≤ hi
  k : σ.vars "k" + md = σ.vars "i1" + σ.vars "i2"
  T : ∃ g, σ.arrs "T" = arrOf N g ∧ (∀ t < lo, g t = g0 t) ∧
    ∀ t, lo ≤ t → t < σ.vars "k" →
      g t = (List.merge (seg fA lo md) (seg fA md hi) le).getD (t - lo) 0
  rest : (List.merge (seg fA lo md) (seg fA md hi) le).drop (σ.vars "k" - lo) =
    List.merge (seg fA (σ.vars "i1") md) (seg fA (σ.vars "i2") hi) le

variable {wd lo md hi : ℕ} {fA g0 : ℕ → ℕ}

/-- The invariant after `T[k] := v` and one of `i1`, `i2` moved on. -/
theorem MInv.next {σ σ' : Env} (I : MInv le Ctx N n wd lo md hi fA g0 σ) (hctx : Ctx σ')
    {a1 a2 v : ℕ} (hv : ∀ x, x = "n" ∨ x = "wd" ∨ x = "i" ∨ x = "md" ∨ x = "hi" →
      σ'.vars x = σ.vars x)
    (h1 : σ'.vars "i1" = a1) (h2 : σ'.vars "i2" = a2) (hk : σ'.vars "k" = σ.vars "k" + 1)
    (ha1 : σ.vars "i1" ≤ a1) (ha1' : a1 ≤ md) (ha2 : σ.vars "i2" ≤ a2) (ha2' : a2 ≤ hi)
    (hsum : a1 + a2 = σ.vars "i1" + σ.vars "i2" + 1)
    (hA : σ'.arrs "A" = σ.arrs "A") (hT : σ'.arrs "T" = (σ.arrs "T").set (σ.vars "k") v)
    (hM : (List.merge (seg fA lo md) (seg fA md hi) le).getD (σ.vars "k" - lo) 0 = v ∧
      (List.merge (seg fA lo md) (seg fA md hi) le).drop (σ.vars "k" - lo + 1) =
        List.merge (seg fA a1 md) (seg fA a2 hi) le) :
    MInv le Ctx N n wd lo md hi fA g0 σ' := by
  obtain ⟨g, hg, hg0, hgM⟩ := I.T
  have hlo : lo ≤ σ.vars "k" := by have := I.k; have := I.lo_i1; have := I.md_i2; omega
  refine ⟨by rw [hv _ (by simp), I.n_eq], by rw [hv _ (by simp), I.wd_eq],
    by rw [hv _ (by simp), I.i_eq], by rw [hv _ (by simp), I.md_eq], by rw [hv _ (by simp), I.hi_eq],
    by rw [hA, I.A_eq], hctx,
    by rw [h1]; exact I.lo_i1.trans ha1, by rw [h1]; exact ha1', by rw [h2]; exact I.md_i2.trans ha2,
    by rw [h2]; exact ha2', by rw [hk, h1, h2]; have := I.k; omega,
    ⟨fun t => if t = σ.vars "k" then v else g t, by rw [hT, hg, set_arrOf], fun t ht => ?_,
      fun t ht1 ht2 => ?_⟩, ?_⟩
  · show (if t = σ.vars "k" then v else g t) = g0 t
    rw [if_neg (by omega)]; exact hg0 t ht
  · show (if t = σ.vars "k" then v else g t) = _
    rw [hk] at ht2
    by_cases e : t = σ.vars "k"
    · rw [if_pos e, e, hM.1]
    · rw [if_neg e]; exact hgM t ht1 (by omega)
  · rw [hk, h1, h2, show σ.vars "k" + 1 - lo = σ.vars "k" - lo + 1 by omega]
    exact hM.2

theorem run_incr {σ : Env} (x : String) (h : σ.vars x + 1 < B) :
    Run B (incr x) σ (σ.setVar x (σ.vars x + 1)) 4 :=
  (Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) h)).mono (by simp)

theorem condLt_vars {σ : Env} {x y : String} (hx : σ.vars x < B) (hy : σ.vars y < B) :
    (Cond.lt (V x) (V y)).evalB B σ = some (decide (σ.vars x < σ.vars y)) :=
  evalB_condLt (evalB_var hx) (evalB_var hy)

/-- **One step of the merge.** -/
theorem run_mstep (hc : Cmp B cmp le Ctx Key Kc) (hkey : ∀ t < n, Key (fA t)) (hhi : hi ≤ n)
    (hnN : n ≤ N) (hNB : N < B) {σ : Env} (I : MInv le Ctx N n wd lo md hi fA g0 σ)
    (hk : σ.vars "k" < hi) :
    ∃ σ', Run B (mstep cmp) σ σ' (Kc + 30) ∧ MInv le Ctx N n wd lo md hi fA g0 σ' ∧
      σ'.vars "k" = σ.vars "k" + 1 := by
  obtain ⟨g, hg, -, -⟩ := I.T
  have hkI := I.k
  have hlen : (σ.arrs "T").length = N := by rw [hg]; simp
  have hmdv := I.md_eq
  have hhiv := I.hi_eq
  have hb1 := I.i1_md
  have hb2 := I.i2_hi
  have hb3 := I.md_i2
  have hcA := condLt_vars (B := B) (σ := σ) (x := "i1") (y := "md") (by omega) (by omega)
  have hcB := condLt_vars (B := B) (σ := σ) (x := "i2") (y := "hi") (by omega) (by omega)
  have hrest := I.rest
  have hlo : lo ≤ σ.vars "k" := by have := I.lo_i1; omega
  by_cases h1 : σ.vars "i1" < md
  · rw [← hmdv] at h1
    rw [show decide (σ.vars "i1" < σ.vars "md") = true by simpa using h1] at hcA
    rw [hmdv] at h1
    by_cases h2 : σ.vars "i2" < hi
    · rw [← hhiv] at h2
      rw [show decide (σ.vars "i2" < σ.vars "hi") = true by simpa using h2] at hcB
      rw [hhiv] at h2
      have r1 : Run B (.assign "x" (.get "A" (V "i1"))) σ (σ.setVar "x" (fA (σ.vars "i1"))) 3 :=
        (Run.assign (evalB_get (evalB_var (by omega))
          (by rw [I.A_eq]; exact getElem?_arrOf _ (by omega))
          (hc.keyB _ (hkey _ (by omega))))).mono (by simp)
      set σ1 := σ.setVar "x" (fA (σ.vars "i1")) with hσ1
      have r2 : Run B (.assign "y" (.get "A" (V "i2"))) σ1
          (σ1.setVar "y" (fA (σ.vars "i2"))) 3 :=
        (Run.assign (evalB_get (evalB_var (by simp [σ1]; omega))
          (by simp only [σ1, arrs_setVar, vars_setVar]; rw [I.A_eq]
              exact getElem?_arrOf _ (by simp; omega))
          (hc.keyB _ (hkey _ (by omega))))).mono (by simp)
      set σ2 := σ1.setVar "y" (fA (σ.vars "i2")) with hσ2
      obtain ⟨σ3, r3, hc3, hv3, ha3, hctx3⟩ := hc.step (σ := σ2)
        (hc.ctx_setVar (hc.ctx_setVar I.ctx (by decide) _) (by decide) _)
        (by simp [σ2, σ1]; exact hkey _ (by omega)) (by simp [σ2, σ1]; exact hkey _ (by omega))
      have hv3' : ∀ v, v ∈ sortVars ∨ v = "n" → v ≠ "x" → v ≠ "y" → σ3.vars v = σ.vars v := by
        intro v hv hx hy; rw [hv3 v hv]; simp [σ2, σ1, hx, hy]
      have hkv : σ3.vars "k" = σ.vars "k" := hv3' "k" (by decide) (by decide) (by decide)
      have hA3 : σ3.arrs "A" = σ.arrs "A" := by rw [ha3]; simp [σ2, σ1]
      have hT3 : σ3.arrs "T" = σ.arrs "T" := by rw [ha3]; simp [σ2, σ1]
      have hseg1 := seg_cons fA h1
      have hseg2 := seg_cons fA h2
      by_cases hle : le (fA (σ.vars "i1")) (fA (σ.vars "i2")) = true
      · have hcc : (Cond.eq (V "c") (.lit 1)).evalB B σ3 = some true := by
          rw [evalB_condEq (evalB_var (by rw [hc3]; split_ifs <;> omega)) (evalB_lit (by omega))]
          simp [hc3, σ2, σ1, hle]
        have r4 : Run B (.store "T" (V "k") (V "x")) σ3
            (σ3.setArr "T" (σ.vars "k") (fA (σ.vars "i1"))) 3 :=
          (Run.store (evalB_var (by rw [hkv]; omega))
            (evalB_var (by rw [hv3 "x" (by decide)]; simp [σ2, σ1]; exact hc.keyB _ (hkey _ (by omega))))
            (by rw [hT3, hlen]; omega)).mono (by simp)
            |>.congr (by rw [hkv, hv3 "x" (by decide)]; simp [σ2, σ1])
        set σ4 := σ3.setArr "T" (σ.vars "k") (fA (σ.vars "i1")) with hσ4
        have r5 := run_incr (B := B) (σ := σ4) "i1"
          (by simp [σ4]; rw [hv3' "i1" (by decide) (by decide) (by decide)]; omega)
        set σ5 := σ4.setVar "i1" (σ4.vars "i1" + 1) with hσ5
        have r6 := run_incr (B := B) (σ := σ5) "k" (by simp [σ5, σ4]; rw [hkv]; omega)
        refine ⟨_, ((Run.ite_true hcA (Run.ite_true hcB (r1.seq (r2.seq (r3.seq
          (Run.ite_true hcc (r4.seq r5))))))).seq r6).mono (by simp; omega), ?_, ?_⟩
        · refine I.next ?_ (a1 := σ.vars "i1" + 1) (a2 := σ.vars "i2") (v := fA (σ.vars "i1"))
            (fun x hx => ?_) ?_ ?_ ?_ (by omega) (by omega) le_rfl (by omega) (by omega) ?_ ?_ ?_
          · exact hc.ctx_setVar (hc.ctx_setVar (hc.ctx_setArr hctx3 (by simp) _ _) (by decide) _)
              (by decide) _
          · have hx' : x ≠ "k" ∧ x ≠ "i1" := by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
            simp only [σ5, σ4, vars_setVar, vars_setArr, if_neg hx'.1, if_neg hx'.2]
            exact hv3' x (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
              (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
              (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
          · simp [σ5, σ4]; rw [hv3' "i1" (by decide) (by decide) (by decide)]
          · simp [σ5, σ4]; exact hv3' "i2" (by decide) (by decide) (by decide)
          · simp [σ5, σ4]; exact hkv
          · simp [σ5, σ4, hA3]
          · simp [σ5, σ4, hT3]
          · exact drop_cons_eq (by rw [hrest, hseg1, hseg2, List.cons_merge_cons_pos _ _ _ hle])
        · simp [σ5, σ4]; exact hkv
      · have hcc : (Cond.eq (V "c") (.lit 1)).evalB B σ3 = some false := by
          rw [evalB_condEq (evalB_var (by rw [hc3]; split_ifs <;> omega)) (evalB_lit (by omega))]
          simp [hc3, σ2, σ1, hle]
        have r4 : Run B (.store "T" (V "k") (V "y")) σ3
            (σ3.setArr "T" (σ.vars "k") (fA (σ.vars "i2"))) 3 :=
          (Run.store (evalB_var (by rw [hkv]; omega))
            (evalB_var (by rw [hv3 "y" (by decide)]; simp [σ2, σ1]; exact hc.keyB _ (hkey _ (by omega))))
            (by rw [hT3, hlen]; omega)).mono (by simp)
            |>.congr (by rw [hkv, hv3 "y" (by decide)]; simp [σ2, σ1])
        set σ4 := σ3.setArr "T" (σ.vars "k") (fA (σ.vars "i2")) with hσ4
        have r5 := run_incr (B := B) (σ := σ4) "i2"
          (by simp [σ4]; rw [hv3' "i2" (by decide) (by decide) (by decide)]; omega)
        set σ5 := σ4.setVar "i2" (σ4.vars "i2" + 1) with hσ5
        have r6 := run_incr (B := B) (σ := σ5) "k" (by simp [σ5, σ4]; rw [hkv]; omega)
        refine ⟨_, ((Run.ite_true hcA (Run.ite_true hcB (r1.seq (r2.seq (r3.seq
          (Run.ite_false hcc (r4.seq r5))))))).seq r6).mono (by simp; omega), ?_, ?_⟩
        · refine I.next ?_ (a1 := σ.vars "i1") (a2 := σ.vars "i2" + 1) (v := fA (σ.vars "i2"))
            (fun x hx => ?_) ?_ ?_ ?_ le_rfl (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
          · exact hc.ctx_setVar (hc.ctx_setVar (hc.ctx_setArr hctx3 (by simp) _ _) (by decide) _)
              (by decide) _
          · have hx' : x ≠ "k" ∧ x ≠ "i2" := by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
            simp only [σ5, σ4, vars_setVar, vars_setArr, if_neg hx'.1, if_neg hx'.2]
            exact hv3' x (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
              (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
              (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
          · simp [σ5, σ4]; exact hv3' "i1" (by decide) (by decide) (by decide)
          · simp [σ5, σ4]; rw [hv3' "i2" (by decide) (by decide) (by decide)]
          · simp [σ5, σ4]; exact hkv
          · simp [σ5, σ4, hA3]
          · simp [σ5, σ4, hT3]
          · exact drop_cons_eq (by rw [hrest, hseg1, hseg2, List.cons_merge_cons_neg _ _ _ hle])
        · simp [σ5, σ4]; exact hkv
    · -- the second block is used up
      rw [← hhiv] at h2
      rw [show decide (σ.vars "i2" < σ.vars "hi") = false by simpa using h2] at hcB
      rw [hhiv] at h2
      have he2 : seg fA (σ.vars "i2") hi = [] := seg_empty fA (by omega)
      have hseg1 := seg_cons fA h1
      have r4 : Run B (.store "T" (V "k") (.get "A" (V "i1"))) σ
          (σ.setArr "T" (σ.vars "k") (fA (σ.vars "i1"))) 4 :=
        (Run.store (evalB_var (by omega))
          (evalB_get (evalB_var (by omega)) (by rw [I.A_eq]; exact getElem?_arrOf _ (by omega))
            (hc.keyB _ (hkey _ (by omega))))
          (by rw [hlen]; omega)).mono (by simp)
      set σ4 := σ.setArr "T" (σ.vars "k") (fA (σ.vars "i1")) with hσ4
      have r5 := run_incr (B := B) (σ := σ4) "i1" (by simp [σ4]; omega)
      set σ5 := σ4.setVar "i1" (σ4.vars "i1" + 1) with hσ5
      have r6 := run_incr (B := B) (σ := σ5) "k" (by simp [σ5, σ4]; omega)
      refine ⟨_, ((Run.ite_true hcA (Run.ite_false hcB (r4.seq r5))).seq r6).mono (by simp),
        ?_, ?_⟩
      · refine I.next ?_ (a1 := σ.vars "i1" + 1) (a2 := σ.vars "i2") (v := fA (σ.vars "i1"))
          (fun x hx => ?_) ?_ ?_ ?_ (by omega) (by omega) le_rfl (by omega) (by omega) ?_ ?_ ?_
        · exact hc.ctx_setVar (hc.ctx_setVar (hc.ctx_setArr I.ctx (by simp) _ _) (by decide) _)
            (by decide) _
        · have hx' : x ≠ "k" ∧ x ≠ "i1" := by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
          simp only [σ5, σ4, vars_setVar, vars_setArr, if_neg hx'.1, if_neg hx'.2]
        · simp [σ5, σ4]
        · simp [σ5, σ4]
        · simp [σ5, σ4]
        · simp [σ5, σ4]
        · simp [σ5, σ4]
        · exact drop_cons_eq (by rw [hrest, hseg1, he2, List.merge_right, List.merge_right])
      · simp [σ5, σ4]
  · -- the first block is used up
    have h1' : σ.vars "i1" = md := by omega
    have h2 : σ.vars "i2" < hi := by omega
    rw [← hmdv] at h1
    rw [show decide (σ.vars "i1" < σ.vars "md") = false by simpa using h1] at hcA
    have he1 : seg fA (σ.vars "i1") md = [] := seg_empty fA (by omega)
    have hseg2 := seg_cons fA h2
    have r4 : Run B (.store "T" (V "k") (.get "A" (V "i2"))) σ
        (σ.setArr "T" (σ.vars "k") (fA (σ.vars "i2"))) 4 :=
      (Run.store (evalB_var (by omega))
        (evalB_get (evalB_var (by omega)) (by rw [I.A_eq]; exact getElem?_arrOf _ (by omega))
          (hc.keyB _ (hkey _ (by omega))))
        (by rw [hlen]; omega)).mono (by simp)
    set σ4 := σ.setArr "T" (σ.vars "k") (fA (σ.vars "i2")) with hσ4
    have r5 := run_incr (B := B) (σ := σ4) "i2" (by simp [σ4]; omega)
    set σ5 := σ4.setVar "i2" (σ4.vars "i2" + 1) with hσ5
    have r6 := run_incr (B := B) (σ := σ5) "k" (by simp [σ5, σ4]; omega)
    refine ⟨_, ((Run.ite_false hcA (r4.seq r5)).seq r6).mono (by simp), ?_, ?_⟩
    · refine I.next ?_ (a1 := σ.vars "i1") (a2 := σ.vars "i2" + 1) (v := fA (σ.vars "i2"))
        (fun x hx => ?_) ?_ ?_ ?_ le_rfl (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
      · exact hc.ctx_setVar (hc.ctx_setVar (hc.ctx_setArr I.ctx (by simp) _ _) (by decide) _)
          (by decide) _
      · have hx' : x ≠ "k" ∧ x ≠ "i2" := by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
        simp only [σ5, σ4, vars_setVar, vars_setArr, if_neg hx'.1, if_neg hx'.2]
      · simp [σ5, σ4]
      · simp [σ5, σ4]
      · simp [σ5, σ4]
      · simp [σ5, σ4]
      · simp [σ5, σ4]
      · exact drop_cons_eq (by rw [hrest, hseg2, he1, List.nil_merge, List.nil_merge])
    · simp [σ5, σ4]

/-- **The merge**: `while k < hi do mstep`. -/
theorem run_merge (hc : Cmp B cmp le Ctx Key Kc) (hkey : ∀ t < n, Key (fA t)) (hhi : hi ≤ n)
    (hnN : n ≤ N) (hNB : N < B) {σ : Env} (I : MInv le Ctx N n wd lo md hi fA g0 σ)
    (hk : σ.vars "k" ≤ hi) :
    ∃ σ', Run B (.while (.lt (V "k") (V "hi")) (mstep cmp)) σ σ'
      ((Kc + 34) * (hi - σ.vars "k") + 4) ∧ MInv le Ctx N n wd lo md hi fA g0 σ' ∧
      σ'.vars "k" = hi := by
  obtain ⟨σ', hr, ⟨I', hk'⟩, hf⟩ := Run.while_count (B := B) (b := .lt (V "k") (V "hi"))
    (c := mstep cmp) (fun τ => MInv le Ctx N n wd lo md hi fA g0 τ ∧ τ.vars "k" ≤ hi)
    (fun τ => hi - τ.vars "k") (Kc + 30)
    (fun τ ⟨J, hJ⟩ => evalB_condLt_vars (by omega) (by rw [J.hi_eq]; omega))
    (fun τ ⟨J, hJ⟩ hb => by
      have hlt := lt_of_condLt_true hb
      rw [J.hi_eq] at hlt
      obtain ⟨τ', hr, J', hk'⟩ := run_mstep hc hkey hhi hnN hNB J hlt
      exact ⟨τ', hr, ⟨J', by omega⟩, by omega⟩) ⟨I, hk⟩
  have hge := le_of_condLt_false hf
  rw [I'.hi_eq] at hge
  exact ⟨σ', hr.mono (by simp; nlinarith), I', by omega⟩

/-- `x := min (a + b) c` -/
def minAssign (x a b c : String) : Com :=
  .ite (.lt (.add (V a) (V b)) (V c)) (.assign x (.add (V a) (V b))) (.assign x (V c))

theorem run_minAssign {σ : Env} (x a b c : String) (hab : σ.vars a + σ.vars b < B)
    (hc : σ.vars c < B) :
    Run B (minAssign x a b c) σ (σ.setVar x (min (σ.vars a + σ.vars b) (σ.vars c))) 10 := by
  have he : (Expr.add (V a) (V b)).evalB B σ = some (σ.vars a + σ.vars b) :=
    evalB_bin (evalB_var (by omega)) (evalB_var (by omega)) hab
  have hcond := evalB_condLt (B := B) he (evalB_var (x := c) hc)
  by_cases h : σ.vars a + σ.vars b < σ.vars c
  · rw [min_eq_left h.le]
    exact (Run.ite_true (by rw [hcond]; simp [h]) (Run.assign he)).mono (by simp)
  · rw [min_eq_right (by omega)]
    exact (Run.ite_false (by rw [hcond]; simp [h]) (Run.assign (evalB_var hc))).mono (by simp)

/-- The merge of the block at `i`: `md = min (i + wd) n`, `hi = min (md + wd) n`. -/
def mblock (cmp : Com) : Com :=
  .seq (minAssign "md" "i" "wd" "n") <| .seq (minAssign "hi" "md" "wd" "n") <|
  .seq (.assign "i1" (V "i")) <| .seq (.assign "i2" (V "md")) <| .seq (.assign "k" (V "i")) <|
  .seq (.while (.lt (V "k") (V "hi")) (mstep cmp)) (.assign "i" (V "hi"))

/-- **The merge of one block.** -/
theorem run_mblock (hc : Cmp B cmp le Ctx Key Kc) (hkey : ∀ t < n, Key (fA t)) (hnN : n ≤ N)
    (hB : 4 * N + 4 < B) (hwd : wd ≤ 2 * n) {σ : Env} (hn : σ.vars "n" = n)
    (hw : σ.vars "wd" = wd) (hlo : σ.vars "i" = lo) (hlon : lo < n) (hA : σ.arrs "A" = arrOf N fA)
    {g : ℕ → ℕ} (hT : σ.arrs "T" = arrOf N g) (hctx : Ctx σ) :
    ∃ σ', Run B (mblock cmp) σ σ'
      ((Kc + 34) * (min (min (lo + wd) n + wd) n - lo) + 32) ∧
      σ'.vars "n" = n ∧ σ'.vars "wd" = wd ∧ σ'.vars "i" = min (min (lo + wd) n + wd) n ∧
      σ'.arrs "A" = arrOf N fA ∧ Ctx σ' ∧
      ∃ g', σ'.arrs "T" = arrOf N g' ∧ (∀ t < lo, g' t = g t) ∧
        ∀ t, lo ≤ t → t < min (min (lo + wd) n + wd) n →
          g' t = (List.merge (seg fA lo (min (lo + wd) n))
            (seg fA (min (lo + wd) n) (min (min (lo + wd) n + wd) n)) le).getD (t - lo) 0 := by
  set md := min (lo + wd) n with hmd
  set hi := min (md + wd) n with hhi
  have r1 := run_minAssign (B := B) (σ := σ) "md" "i" "wd" "n" (by omega) (by omega)
  rw [hlo, hw, hn] at r1
  set σ1 := σ.setVar "md" md with hσ1
  have r2 := run_minAssign (B := B) (σ := σ1) "hi" "md" "wd" "n" (by simp [σ1]; omega)
    (by simp [σ1]; omega)
  simp only [σ1, vars_setVar, if_pos, if_neg (show ("wd" : String) ≠ "md" by decide),
    if_neg (show ("n" : String) ≠ "md" by decide), hw, hn] at r2
  set σ2 := σ1.setVar "hi" hi with hσ2
  have r3 : Run B (.assign "i1" (V "i")) σ2 (σ2.setVar "i1" lo) 2 :=
    (Run.assign (evalB_var (by simp [σ2, σ1, hlo]; omega))).congr (by simp [σ2, σ1, hlo])
  set σ3 := σ2.setVar "i1" lo with hσ3
  have r4 : Run B (.assign "i2" (V "md")) σ3 (σ3.setVar "i2" md) 2 :=
    (Run.assign (evalB_var (by simp [σ3, σ2, σ1]; omega))).congr (by simp [σ3, σ2, σ1])
  set σ4 := σ3.setVar "i2" md with hσ4
  have r5 : Run B (.assign "k" (V "i")) σ4 (σ4.setVar "k" lo) 2 :=
    (Run.assign (evalB_var (by simp [σ4, σ3, σ2, σ1, hlo]; omega))).congr
      (by simp [σ4, σ3, σ2, σ1, hlo])
  set σ5 := σ4.setVar "k" lo with hσ5
  have hctx5 : Ctx σ5 := hc.ctx_setVar (hc.ctx_setVar (hc.ctx_setVar (hc.ctx_setVar
    (hc.ctx_setVar hctx (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have I5 : MInv le Ctx N n wd lo md hi fA g σ5 := by
    refine ⟨by simp [σ5, σ4, σ3, σ2, σ1, hn], by simp [σ5, σ4, σ3, σ2, σ1, hw],
      by simp [σ5, σ4, σ3, σ2, σ1, hlo], by simp [σ5, σ4, σ3, σ2, σ1],
      by simp [σ5, σ4, σ3, σ2, σ1], by simp [σ5, σ4, σ3, σ2, σ1, hA], hctx5,
      by simp [σ5, σ4, σ3, σ2, σ1], by simp [σ5, σ4, σ3, σ2, σ1]; omega,
      by simp [σ5, σ4, σ3, σ2, σ1], by simp [σ5, σ4, σ3, σ2, σ1]; omega,
      by simp [σ5, σ4, σ3, σ2, σ1],
      ⟨g, by simp [σ5, σ4, σ3, σ2, σ1, hT], fun _ _ => rfl, fun t h1 h2 => by
        simp [σ5, σ4, σ3, σ2, σ1] at h2; omega⟩, ?_⟩
    simp [σ5, σ4, σ3, σ2, σ1]
  obtain ⟨σ6, r6, I6, hk6⟩ := run_merge hc hkey (by omega) hnN (by omega) I5
    (by simp [σ5]; omega)
  have r7 : Run B (.assign "i" (V "hi")) σ6 (σ6.setVar "i" hi) 2 :=
    (Run.assign (evalB_var (by rw [I6.hi_eq]; omega))).congr (by rw [I6.hi_eq])
  obtain ⟨g', hg', hg0, hgM⟩ := I6.T
  refine ⟨σ6.setVar "i" hi, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono
    (by simp [σ5]; omega), by simp [I6.n_eq], by simp [I6.wd_eq], by simp,
    by simp [I6.A_eq], hc.ctx_setVar I6.ctx (by decide) _, g', by simp [hg'], hg0,
    fun t h1 h2 => hgM t h1 (by omega)⟩

theorem getD_drop_eq (l : List ℕ) (j t : ℕ) : (l.drop j).getD t 0 = l.getD (j + t) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_append_lt {l l' : List ℕ} {t : ℕ} (h : t < l.length) :
    (l ++ l').getD t 0 = l.getD t 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- A pass at a block start: the merge of the block, then the pass on the rest. -/
theorem pass_block (fA : ℕ → ℕ) {lo n wd : ℕ} (hlo : lo < n) (hw : 0 < wd) :
    passL le wd (seg fA lo n) = List.merge (seg fA lo (min (lo + wd) n))
      (seg fA (min (lo + wd) n) (min (min (lo + wd) n + wd) n)) le ++
      passL le wd (seg fA (min (min (lo + wd) n + wd) n) n) := by
  have hne : seg fA lo n ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  rw [passL_cons le hw hne, seg_take fA lo n wd, seg_drop fA lo n wd, seg_take fA (lo + wd) n wd,
    seg_drop fA lo n (2 * wd)]
  have e1 : seg fA (lo + wd) (min (lo + wd + wd) n) =
      seg fA (min (lo + wd) n) (min (min (lo + wd) n + wd) n) := by
    by_cases h : lo + wd < n
    · rw [min_eq_left h.le]
    · rw [seg_empty fA (show min (lo + wd + wd) n ≤ lo + wd by omega),
        seg_empty fA (show min (min (lo + wd) n + wd) n ≤ min (lo + wd) n by omega)]
  have e2 : seg fA (lo + 2 * wd) n = seg fA (min (min (lo + wd) n + wd) n) n := by
    by_cases h : lo + 2 * wd ≤ n
    · congr 1; omega
    · rw [seg_empty fA (show n ≤ lo + 2 * wd by omega),
        seg_empty fA (show n ≤ min (min (lo + wd) n + wd) n by omega)]
  rw [e1, e2]

/-- The state of a pass of width `wd` over `A[0..n)` into `T`. -/
structure PInv (le : ℕ → ℕ → Bool) (Ctx : Env → Prop) (N n wd : ℕ) (fA : ℕ → ℕ) (σ : Env) :
    Prop where
  n_eq : σ.vars "n" = n
  wd_eq : σ.vars "wd" = wd
  i_le : σ.vars "i" ≤ n
  A_eq : σ.arrs "A" = arrOf N fA
  ctx : Ctx σ
  T : ∃ g, σ.arrs "T" = arrOf N g ∧ ∀ t < σ.vars "i", g t = (passL le wd (seg fA 0 n)).getD t 0
  rest : (passL le wd (seg fA 0 n)).drop (σ.vars "i") = passL le wd (seg fA (σ.vars "i") n)

/-- One pass: the blocks of width `wd` merged in pairs, from `A` into `T`. -/
def mpass (cmp : Com) : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) (mblock cmp))

/-- **One pass.** -/
theorem run_mpass (hc : Cmp B cmp le Ctx Key Kc) (hkey : ∀ t < n, Key (fA t)) (hnN : n ≤ N)
    (hB : 4 * N + 4 < B) (hw0 : 0 < wd) (hwd : wd ≤ 2 * n) {σ : Env} (hn : σ.vars "n" = n)
    (hw : σ.vars "wd" = wd) (hA : σ.arrs "A" = arrOf N fA) {g : ℕ → ℕ}
    (hT : σ.arrs "T" = arrOf N g) (hctx : Ctx σ) :
    ∃ σ' g', Run B (mpass cmp) σ σ' ((Kc + 70) * n + 6) ∧ σ'.vars "n" = n ∧
      σ'.vars "wd" = wd ∧ σ'.arrs "A" = arrOf N fA ∧ Ctx σ' ∧ σ'.arrs "T" = arrOf N g' ∧
      ∀ t < n, g' t = (passL le wd (seg fA 0 n)).getD t 0 := by
  have r0 : Run B (.assign "i" (.lit 0)) σ (σ.setVar "i" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have P0 : PInv le Ctx N n wd fA (σ.setVar "i" 0) :=
    ⟨by simp [hn], by simp [hw], by simp, by simp [hA], hc.ctx_setVar hctx (by decide) _,
      ⟨g, by simp [hT], fun t ht => by simp at ht⟩, by simp⟩
  obtain ⟨σ', K, hr, P', hf, hK⟩ := Run.while_potential (B := B) (b := .lt (V "i") (V "n"))
    (c := mblock cmp) (PInv le Ctx N n wd fA) (fun τ => (Kc + 70) * (n - τ.vars "i"))
    (fun τ J => evalB_condLt_vars (by have := J.i_le; omega) (by rw [J.n_eq]; omega))
    (fun τ J hb => by
      have hlt := lt_of_condLt_true hb
      rw [J.n_eq] at hlt
      obtain ⟨g1, hg1, hg1o⟩ := J.T
      obtain ⟨τ', hr, hn', hw', hi', hA', hctx', g', hg', hg0, hgM⟩ :=
        run_mblock hc hkey hnN hB hwd J.n_eq J.wd_eq rfl hlt J.A_eq hg1 J.ctx
      set lo := τ.vars "i"
      set md := min (lo + wd) n
      set hi := min (md + wd) n
      have hlohi : lo < hi := by omega
      have hrest := J.rest
      rw [pass_block fA hlt hw0] at hrest
      have hMlen : (List.merge (seg fA lo md) (seg fA md hi) le).length = hi - lo := by
        simp only [List.length_merge, length_seg]; omega
      refine ⟨τ', _, hr, ⟨hn', hw', by rw [hi']; omega, hA', hctx', ⟨g', hg', fun t ht => ?_⟩, ?_⟩,
        ?_⟩
      · rw [hi'] at ht
        by_cases h : t < lo
        · rw [hg0 t h]; exact hg1o t h
        · rw [hgM t (by omega) ht]
          have e := congrArg (fun l => l.getD (t - lo) 0) hrest
          simp only [getD_drop_eq] at e
          rw [show lo + (t - lo) = t by omega, getD_append_lt (by rw [hMlen]; omega)] at e
          exact e.symm
      · rw [hi', show hi = lo + (hi - lo) by omega, ← List.drop_drop, hrest,
          List.drop_left' hMlen, show lo + (hi - lo) = hi by omega]
      · simp only [size_condLt, size_var]
        rw [hi']
        have e : n - lo = (n - hi) + (hi - lo) := by omega
        rw [e, Nat.mul_add]
        have h36 : 36 ≤ 36 * (hi - lo) := by omega
        have hring : (Kc + 70) * (hi - lo) = (Kc + 34) * (hi - lo) + 36 * (hi - lo) := by ring
        omega) P0
  have hge := le_of_condLt_false hf
  rw [P'.n_eq] at hge
  have hin : σ'.vars "i" = n := le_antisymm P'.i_le hge
  obtain ⟨g', hg', hgo⟩ := P'.T
  refine ⟨σ', g', (r0.seq hr).mono ?_, P'.n_eq, P'.wd_eq, P'.A_eq, P'.ctx, hg', fun t ht => hgo t
    (by omega)⟩
  simp only [size_condLt, size_var] at hK
  simp only [vars_setVar, if_pos, Nat.sub_zero] at hK
  omega

/-- `A[k] := T[k]` for `k < n`. -/
def copyAT : Com :=
  .seq (.assign "k" (.lit 0)) (.while (.lt (V "k") (V "n")) (.seq (.store "A" (V "k") (.get "T" (V "k")))
    (incr "k")))

/-- **The copy back.** -/
theorem run_copy (hc : Cmp B cmp le Ctx Key Kc) (hnN : n ≤ N) (hNB : N + 1 < B) {σ : Env}
    (hn : σ.vars "n" = n) {f g : ℕ → ℕ} (hA : σ.arrs "A" = arrOf N f) (hT : σ.arrs "T" = arrOf N g)
    (hgB : ∀ t < n, g t < B) (hctx : Ctx σ) :
    ∃ σ', Run B copyAT σ σ' (12 * n + 6) ∧
      σ'.arrs "A" = arrOf N (fun t => if t < n then g t else f t) ∧ σ'.arrs "T" = arrOf N g ∧
      σ'.vars "n" = n ∧ σ'.vars "wd" = σ.vars "wd" ∧ Ctx σ' := by
  have r0 : Run B (.assign "k" (.lit 0)) σ (σ.setVar "k" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  let J : Env → Prop := fun τ => τ.vars "k" ≤ n ∧ τ.vars "n" = n ∧ τ.vars "wd" = σ.vars "wd" ∧
    τ.arrs "A" = arrOf N (fun t => if t < τ.vars "k" then g t else f t) ∧
    τ.arrs "T" = arrOf N g ∧ Ctx τ
  obtain ⟨σ', hr, ⟨hk', hn', hw', hA', hT', hctx'⟩, hf⟩ := Run.while_count (B := B)
    (b := .lt (V "k") (V "n"))
    (c := .seq (.store "A" (V "k") (.get "T" (V "k"))) (incr "k")) J (fun τ => n - τ.vars "k") 8
    (fun τ hJ => evalB_condLt_vars (by have := hJ.1; omega) (by rw [hJ.2.1]; omega))
    (fun τ ⟨hk, hn1, hw1, hA1, hT1, hc1⟩ hb => by
      have hlt := lt_of_condLt_true hb
      rw [hn1] at hlt
      have r1 : Run B (.store "A" (V "k") (.get "T" (V "k"))) τ
          (τ.setArr "A" (τ.vars "k") (g (τ.vars "k"))) 4 :=
        (Run.store (evalB_var (by omega))
          (evalB_get (evalB_var (by omega)) (by rw [hT1]; exact getElem?_arrOf _ (by omega))
            (hgB _ hlt)) (by rw [hA1]; simp; omega)).mono (by simp)
      have r2 := run_incr (B := B) (σ := τ.setArr "A" (τ.vars "k") (g (τ.vars "k"))) "k"
        (by simp; omega)
      refine ⟨_, (r1.seq r2).mono (by simp), ⟨by simp; omega, by simp [hn1], by simp [hw1], ?_,
        by simp [hT1], hc.ctx_setVar (hc.ctx_setArr hc1 (by simp) _ _) (by decide) _⟩, by simp; omega⟩
      show (τ.setArr "A" (τ.vars "k") (g (τ.vars "k"))).arrs "A" =
        arrOf N (fun t => if t < τ.vars "k" + 1 then g t else f t)
      rw [arrs_setArr, if_pos rfl, hA1, set_arrOf]
      refine arrOf_congr fun t _ => ?_
      by_cases h : t = τ.vars "k"
      · simp [h]
      · simp only [if_neg h]
        by_cases h' : t < τ.vars "k"
        · simp [h', show t < τ.vars "k" + 1 by omega]
        · simp [h', show ¬ t < τ.vars "k" + 1 by omega])
    (σ := σ.setVar "k" 0) ⟨by simp, by simp [hn], by simp, by simp [hA], by simp [hT],
      hc.ctx_setVar hctx (by decide) _⟩
  have hge := le_of_condLt_false hf
  rw [hn'] at hge
  have hkn : σ'.vars "k" = n := le_antisymm hk' hge
  refine ⟨σ', (r0.seq hr).mono (by simp; omega), by rw [hA', hkn], hT', hn', hw', hctx'⟩

/-- **Bottom-up merge sort** of `A[0..n)`, with `T` as scratch space. -/
def msort (cmp : Com) : Com :=
  .seq (.assign "wd" (.lit 1)) (.while (.lt (V "wd") (V "n"))
    (.seq (mpass cmp) (.seq copyAT (.assign "wd" (.add (V "wd") (V "wd"))))))

/-- The cost of the sort: `log₂ n + 1` passes of linear cost. -/
def sortCost (Kc n : ℕ) : ℕ := ((Kc + 82) * n + 20) * (Nat.log 2 n + 1) + 6

theorem mem_seg {f : ℕ → ℕ} {a n : ℕ} (h : a ∈ seg f 0 n) : ∃ s < n, f s = a := by
  unfold seg at h
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  exact ⟨s, by simpa using hs, by simp⟩

/-- **Merge sort**: the keys of `A[0..n)` sorted by `le`, in `O(n log n)` comparisons. -/
theorem run_msort (hc : Cmp B cmp le Ctx Key Kc) (hnN : n ≤ N) (hB : 4 * N + 4 < B) {σ : Env}
    (hn : σ.vars "n" = n) {f0 fT : ℕ → ℕ} (hA : σ.arrs "A" = arrOf N f0)
    (hT : σ.arrs "T" = arrOf N fT) (hkey : ∀ t < n, Key (f0 t)) (hctx : Ctx σ) :
    ∃ σ' f, Run B (msort cmp) σ σ' (sortCost Kc n) ∧ σ'.arrs "A" = arrOf N f ∧
      (seg f 0 n).Perm (seg f0 0 n) ∧ (seg f 0 n).Pairwise (R le) ∧ Ctx σ' := by
  have r0 : Run B (.assign "wd" (.lit 1)) σ (σ.setVar "wd" 1) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hkeyOf : ∀ f : ℕ → ℕ, (seg f 0 n).Perm (seg f0 0 n) → ∀ t < n, Key (f t) := by
    intro f hp t ht
    have hm : f t ∈ seg f 0 n := by
      unfold seg; exact List.mem_map.mpr ⟨t, by simpa using ht, by simp⟩
    obtain ⟨s, hs, hfs⟩ := mem_seg (hp.mem_iff.mp hm)
    rw [← hfs]; exact hkey s hs
  let O : Env → Prop := fun τ => τ.vars "n" = n ∧ (∃ kk, τ.vars "wd" = 2 ^ kk) ∧
    τ.vars "wd" ≤ 2 * n + 1 ∧
    (∃ f, τ.arrs "A" = arrOf N f ∧ (seg f 0 n).Perm (seg f0 0 n) ∧
      Chunks le (τ.vars "wd") (seg f 0 n)) ∧
    (∃ g, τ.arrs "T" = arrOf N g) ∧ Ctx τ
  obtain ⟨σ', hr, ⟨hn', -, -, ⟨f, hf, hperm, hch⟩, -, hctx'⟩, hfalse⟩ := Run.while_count (B := B)
    (b := .lt (V "wd") (V "n")) (c := .seq (mpass cmp) (.seq copyAT (.assign "wd" (.add (V "wd") (V "wd")))))
    O (fun τ => Nat.log 2 n + 1 - Nat.log 2 (τ.vars "wd")) ((Kc + 82) * n + 16)
    (fun τ hO => evalB_condLt_vars (by have := hO.2.2.1; omega) (by rw [hO.1]; omega))
    (fun τ ⟨hn1, ⟨kk, hkk⟩, hwb, ⟨f, hf, hp, hch⟩, ⟨g, hg⟩, hc1⟩ hb => by
      have hlt := lt_of_condLt_true hb
      rw [hn1] at hlt
      have hw0 : 0 < τ.vars "wd" := by rw [hkk]; positivity
      obtain ⟨τ1, g', r1, hn2, hw2, hA2, hc2, hT2, hg'⟩ := run_mpass hc (hkeyOf f hp) hnN hB hw0
        (by omega) hn1 rfl hf hg hc1
      have hout : (passL le (τ.vars "wd") (seg f 0 n)).Perm (seg f 0 n) :=
        passL_perm le _ _ _ rfl
      have hlen : (passL le (τ.vars "wd") (seg f 0 n)).length = n := by
        rw [length_passL]; simp
      have hgB : ∀ t < n, g' t < B := by
        intro t ht
        rw [hg' t ht]
        have hm : (passL le (τ.vars "wd") (seg f 0 n)).getD t 0 ∈ passL le (τ.vars "wd") (seg f 0 n) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
          exact List.getElem_mem _
        obtain ⟨s, hs, hfs⟩ := mem_seg ((hout.trans hp).mem_iff.mp hm)
        rw [← hfs]; exact hc.keyB _ (hkey s hs)
      obtain ⟨τ2, r2, hA3, hT3, hn3, hw3, hc3⟩ := run_copy hc hnN (by omega) hn2 hA2 hT2 hgB hc2
      have r3 : Run B (.assign "wd" (.add (V "wd") (V "wd"))) τ2
          (τ2.setVar "wd" (τ.vars "wd" + τ.vars "wd")) 4 := by
        have h1 : τ2.vars "wd" = τ.vars "wd" := by rw [hw3, hw2]
        have := Run.assign (B := B) (σ := τ2) (x := "wd") (evalB_bin (op := .add)
          (evalB_var (x := "wd") (σ := τ2) (by rw [h1]; omega))
          (evalB_var (x := "wd") (σ := τ2) (by rw [h1]; omega)) (by simp only [Bop.apply_add, h1]; omega))
        rw [h1] at this
        exact this.mono (by simp)
      have hseg : seg (fun t => if t < n then g' t else f t) 0 n =
          passL le (τ.vars "wd") (seg f 0 n) := by
        refine List.ext_getElem (by simp [hlen]) fun t h1 h2 => ?_
        simp only [getElem_seg, zero_add]
        simp at h1
        rw [if_pos h1, hg' t h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
        rfl
      refine ⟨_, (r1.seq (r2.seq r3)).mono (le_of_eq (by ring)), ⟨by simp [hn3],
        ⟨kk + 1, by simp [hkk, pow_succ]; ring⟩,
        by simp; omega, ⟨fun t => if t < n then g' t else f t, by simp [hA3],
          by rw [hseg]; exact hout.trans hp, ?_⟩,
        ⟨g', by simp [hT3]⟩, hc.ctx_setVar hc3 (by decide) _⟩, ?_⟩
      · simp only [vars_setVar, if_pos]
        rw [hseg, show τ.vars "wd" + τ.vars "wd" = 2 * τ.vars "wd" by ring]
        exact chunks_passL hc.trans hc.total hw0 _ _ rfl hch
      · simp only [vars_setVar, if_pos]
        rw [hkk, show 2 ^ kk + 2 ^ kk = 2 ^ (kk + 1) by ring, Nat.log_pow (by norm_num),
          Nat.log_pow (by norm_num)]
        have : kk ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by rw [← hkk]; omega)
        omega)
    (σ := σ.setVar "wd" 1) ⟨by simp [hn], ⟨0, by simp⟩, by simp, ⟨f0, by simp [hA], List.Perm.refl _,
      by simpa using chunks_one le (seg f0 0 n)⟩, ⟨fT, by simp [hT]⟩, hc.ctx_setVar hctx (by decide) _⟩
  have hge := le_of_condLt_false hfalse
  rw [hn'] at hge
  refine ⟨σ', f, (r0.seq hr).mono ?_, hf, hperm, sorted_of_chunks le hch (by simp; omega), hctx'⟩
  simp only [vars_setVar, if_pos, Nat.log_one_right, size_condLt, size_var, sortCost, Nat.sub_zero]
  apply le_of_eq
  ring

end MSort

/-! ### The total weighted completion time of a sorted order -/

section SeqCost

/-- The sum of the first `k` values. -/
def psum (g : ℕ → ℕ) (k : ℕ) : ℕ := ∑ m ∈ Finset.range k, g m

theorem psum_succ (g : ℕ → ℕ) (k : ℕ) : psum g (k + 1) = psum g k + g k := by
  simp [psum, Finset.sum_range_succ]

/-- The total weighted completion time of the jobs `f 0, f 1, …` run in this order. -/
def seqCost (p w f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, w (f k) * psum (fun m => p (f m)) (k + 1)

theorem opt_congr {p w p' w' : ℕ → ℕ} {n : ℕ} (hp : ∀ j < n, p j = p' j)
    (hw : ∀ j < n, w j = w' j) :
    opt p w n = opt p' w' n := by
  unfold opt
  simp only [hp _ (Fin.isLt _), hw _ (Fin.isLt _)]

/-- **Smith's order is optimal**: run in an order sorted by Smith's comparison, the jobs pay
exactly `opt`. -/
theorem seqCost_eq_opt (p w f : ℕ → ℕ) (n : ℕ) (hperm : (seg f 0 n).Perm (List.range n))
    (hsort : (seg f 0 n).Pairwise (R (smithLe p w))) : seqCost p w f n = opt p w n := by
  have hmem : ∀ k < n, f k ∈ seg f 0 n := fun k hk => by
    unfold seg; exact List.mem_map.mpr ⟨k, by simpa using hk, by simp⟩
  have hlt : ∀ k < n, f k < n := fun k hk => by
    simpa using hperm.mem_iff.mp (hmem k hk)
  have hnd : (seg f 0 n).Nodup := hperm.nodup_iff.mpr List.nodup_range
  have hinj : ∀ a b, a < n → b < n → f a = f b → a = b := by
    intro a b ha hb hab
    have := (List.Nodup.getElem_inj_iff hnd (i := a) (j := b) (hi := by simpa using ha)
      (hj := by simpa using hb)).mp (by simp only [getElem_seg, zero_add]; exact hab)
    exact this
  let e : Fin n → Fin n := fun k => ⟨f k, hlt k k.isLt⟩
  have he : Function.Injective e := fun a b h =>
    Fin.ext (hinj a b a.isLt b.isLt (congrArg Fin.val h))
  let E : Fin n ≃ Fin n := Equiv.ofBijective e (Finite.injective_iff_bijective.mp he)
  have hE : ∀ k, (E k : ℕ) = f k := fun k => rfl
  -- the order of positions
  let S : Fin n → Fin n → Prop := fun i j => E.symm i < E.symm j
  have hS : ∀ i j, S i j → p i * w j ≤ p j * w i := by
    intro i j h
    have h2 := List.pairwise_iff_getElem.mp hsort (E.symm i) (E.symm j)
      (by simp) (by simp) h
    simp only [getElem_seg, zero_add] at h2
    rw [← hE, ← hE, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
    exact smithLe_mul p w h2
  -- the cost as a double sum over positions
  have h1 : seqCost p w f n = ∑ k : Fin n, ∑ m : Fin n,
      if m ≤ k then p (E m) * w (E k) else 0 := by
    unfold seqCost psum
    rw [Finset.sum_range (fun k => w (f k) * ∑ m ∈ Finset.range (k + 1), p (f m))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hr : Finset.range ((k : ℕ) + 1) = (Finset.range n).filter (fun m => m ≤ (k : ℕ)) := by
      ext m; simp only [Finset.mem_range, Finset.mem_filter]; have := k.isLt; omega
    rw [hr, Finset.sum_filter, Finset.mul_sum, Finset.sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hE, hE]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd (Fin.le_def.mpr h1) h2
    · exact absurd (Fin.le_def.mp h2) h1
    · rfl
  -- reindex by `E`
  have h2 : ∑ k : Fin n, ∑ m : Fin n, (if m ≤ k then p (E m) * w (E k) else 0) =
      ∑ j : Fin n, ∑ i : Fin n, if E.symm i ≤ E.symm j then p i * w j else 0 := by
    rw [← E.sum_comp (fun j => ∑ i : Fin n, if E.symm i ≤ E.symm j then p i * w j else 0)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← E.sum_comp (fun i => if E.symm i ≤ E.symm (E k) then p i * w (E k) else 0)]
    simp only [Equiv.symm_apply_apply]
  have h3 : ∀ j : Fin n, ∑ i : Fin n, (if E.symm i ≤ E.symm j then p i * w j else 0) =
      w j * p j + ∑ i : Fin n, if S i j then p i * w j else 0 := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), if_pos le_rfl,
      ← Finset.add_sum_erase _ (fun i => if S i j then p i * w j else 0) (Finset.mem_univ j)]
    simp only [S, lt_irrefl, if_false, zero_add]
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have : E.symm i ≠ E.symm j := fun h => hij (E.symm.injective h)
    by_cases h : E.symm i < E.symm j
    · rw [if_pos h.le, if_pos h]
    · rw [if_neg (fun h' => h (lt_of_le_of_ne h' this)), if_neg h]
  rw [h1, h2, Finset.sum_congr rfl fun j _ => h3 j, Finset.sum_add_distrib, Finset.sum_comm
    (f := fun j i => if S i j then p i * w j else 0)]
  unfold opt
  rw [pairs_eq S (fun i j => p i * w j) (fun i => lt_irrefl _)
    (fun i j h => by
      have : E.symm i ≠ E.symm j := fun h' => h (E.symm.injective h')
      rcases lt_or_gt_of_ne this with h' | h'
      · exact Or.inl h'
      · exact Or.inr h')
    (fun i j h h' => lt_asymm h h') hS]

end SeqCost

/-! ### Smith's comparison in IMP+ -/

section SmithCmp

/-- Smith's comparison of the jobs `x` and `y` read from the arrays `P` and `W`: `c := 1` when
`x` may go before `y`. -/
def cmpSmith : Com :=
  .ite (.eq (.get "W" (V "x")) (.lit 0))
    (.ite (.eq (.get "W" (V "y")) (.lit 0)) (.assign "c" (.lit 1)) (.assign "c" (.lit 0)))
    (.ite (.lt (.mul (.get "P" (V "y")) (.get "W" (V "x"))) (.mul (.get "P" (V "x")) (.get "W" (V "y"))))
      (.assign "c" (.lit 0)) (.assign "c" (.lit 1)))

/-- What the comparison needs: the processing times and the weights in `P` and `W`. -/
def SCtx (N : ℕ) (p w : ℕ → ℕ) (σ : Env) : Prop := σ.arrs "P" = arrOf N p ∧ σ.arrs "W" = arrOf N w

theorem ev_arr {B N : ℕ} {σ : Env} {a : String} {e : Expr} {f : ℕ → ℕ} {k : ℕ}
    (ha : σ.arrs a = arrOf N f) (he : e.evalB B σ = some k) (hk : k < N) (hv : f k < B) :
    (Expr.get a e).evalB B σ = some (f k) :=
  evalB_get he (by rw [ha]; exact getElem?_arrOf f hk) hv

theorem cmpSmith_cmp {B N n : ℕ} {p w : ℕ → ℕ} (hnN : n ≤ N) (hnB : n + 1 < B)
    (hpw : ∀ a b, a < n → b < n → p a * w b < B) (hp : ∀ a < n, p a < B) (hw : ∀ a < n, w a < B) :
    Cmp B cmpSmith (smithLe p w) (SCtx N p w) (fun a => a < n) 19 where
  run σ hσ hx hy := by
    have ex := ev_arr hσ.2 (evalB_var (x := "x") (by omega)) (by omega) (hw _ hx)
    have ey := ev_arr hσ.2 (evalB_var (x := "y") (by omega)) (by omega) (hw _ hy)
    have px := ev_arr hσ.1 (evalB_var (x := "x") (by omega)) (by omega) (hp _ hx)
    have py := ev_arr hσ.1 (evalB_var (x := "y") (by omega)) (by omega) (hp _ hy)
    have l0 : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
    have l1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by omega)
    by_cases h0 : w (σ.vars "x") = 0
    · have c1 : (Cond.eq (.get "W" (V "x")) (.lit 0)).evalB B σ = some true := by
        rw [evalB_condEq ex l0]; simp [h0]
      by_cases h1 : w (σ.vars "y") = 0
      · have c2 : (Cond.eq (.get "W" (V "y")) (.lit 0)).evalB B σ = some true := by
          rw [evalB_condEq ey l0]; simp [h1]
        exact ⟨_, (Run.ite_true c1 (Run.ite_true c2 (Run.assign l1))).mono (by simp),
          by simp [smithLe, h0, h1]⟩
      · have c2 : (Cond.eq (.get "W" (V "y")) (.lit 0)).evalB B σ = some false := by
          rw [evalB_condEq ey l0]; simp [h1]
        exact ⟨_, (Run.ite_true c1 (Run.ite_false c2 (Run.assign l0))).mono (by simp),
          by simp [smithLe, h0, h1]⟩
    · have c1 : (Cond.eq (.get "W" (V "x")) (.lit 0)).evalB B σ = some false := by
        rw [evalB_condEq ex l0]; simp [h0]
      have c2 := evalB_condLt (evalB_bin (op := .mul) py ex (hpw _ _ hy hx))
        (evalB_bin (op := .mul) px ey (hpw _ _ hx hy))
      by_cases h2 : p (σ.vars "y") * w (σ.vars "x") < p (σ.vars "x") * w (σ.vars "y")
      · exact ⟨_, (Run.ite_false c1 (Run.ite_true (by rw [c2]; simp [h2]) (Run.assign l0))).mono
          (by simp), by simp [smithLe, h0]; omega⟩
      · exact ⟨_, (Run.ite_false c1 (Run.ite_false (by rw [c2]; simp [h2]) (Run.assign l1))).mono
          (by simp), by simp [smithLe, h0]; omega⟩
  wvars := by decide
  warrs := rfl
  ctx σ σ' h _ ha := ⟨by rw [ha "P" (by decide) (by decide), h.1],
    by rw [ha "W" (by decide) (by decide), h.2]⟩
  trans := smithLe_trans p w
  total := smithLe_total p w
  keyB a ha := by omega

end SmithCmp

/-! ### Smith's rule as a word RAM program -/

section SmithProgram
open Lax434175Proofs.IsemPrograms (prelude run_prelude arrW getD_le_max)
open Lax434175Proofs.Cost (forLoop run_forLoop)
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub)

/-- `P[j] := p_j; W[j] := w_j; A[j] := j; j := j + 1`, with `p_j` and `w_j` read off the
standard word at `15 j + 5` and at `q + 3 j`. -/
def fillBody : Com :=
  .seq (.store "P" (V "j") (.get "a" (.add (.mul (.lit 15) (V "j")) (.lit 5)))) <|
  .seq (.store "W" (V "j") (.get "a" (.add (V "q") (.mul (.lit 3) (V "j"))))) <|
  .seq (.store "A" (V "j") (V "j")) (incr "j")

/-- `x := A[j]; tm := tm + P[x]; tot := tot + W[x] * tm; j := j + 1` -/
def sumBody : Com :=
  .seq (.assign "x" (.get "A" (V "j"))) <|
  .seq (.assign "tm" (.add (V "tm") (.get "P" (V "x")))) <|
  .seq (.assign "tot" (.add (V "tot") (.mul (.get "W" (V "x")) (V "tm")))) (incr "j")

/-- **Smith's rule**: read the word, sort the jobs by Smith's comparison, add up the weighted
completion times and compare with the threshold. -/
def smithCom : Com :=
  .seq prelude <|
  .seq (.assign "n" (.get "a" (.lit 1))) <|
  .seq (.assign "q" (.add (.mul (.lit 15) (V "n")) (.lit 11))) <|
  .seq (forLoop "j" "n" fillBody) <|
  .seq (msort cmpSmith) <|
  .seq (.assign "tm" (.lit 0)) <| .seq (.assign "tot" (.lit 0)) <|
  .seq (forLoop "j" "n" sumBody) <|
  .seq (.assign "s" (.get "a" (.sub (V "L") (.lit 2)))) <|
  .seq (.assign "d" (.get "a" (.sub (V "L") (.lit 1)))) <|
  .ite (.eq (V "s") (.lit 0)) (.ite (.lt (V "d") (V "tot")) (.write (.lit 0)) (.write (.lit 1)))
    (.write (.lit 0))

/-- The number of jobs a word names. -/
def nU (u : List ℕ) : ℕ := u.getD 1 0

/-- The processing time of job `j` read off a word, `0` past the last job. -/
def pU (u : List ℕ) (j : ℕ) : ℕ := if j < nU u then u.getD (15 * j + 5) 0 else 0

/-- The weight of job `j` read off a word, `0` past the last job. -/
def wU (u : List ℕ) (j : ℕ) : ℕ := if j < nU u then u.getD (15 * nU u + 11 + 3 * j) 0 else 0

/-- The answer the program writes on a word. -/
def ansU (u : List ℕ) : List ℕ :=
  [if u.getD (u.length - 2) 0 = 0 ∧ opt (pU u) (wU u) (nU u) ≤ u.getD (u.length - 1) 0 then 1 else 0]

/-- The words the program reads: the positions it reads exist. -/
def Shape (u : List ℕ) : Prop :=
  nU u ≤ u.length ∧ ∀ j < nU u, 15 * nU u + 11 + 3 * j < u.length + 2

/-- The value bound. -/
def bndS (u : List ℕ) : ℕ := 64 * (u.length + Lax434175.Results.maxEntry u + 2) ^ 4

/-- The cost of the program. -/
def costS (u : List ℕ) : ℕ := 13 * u.length + 50 * nU u + sortCost 19 (nU u) + 50

theorem set_prefix (N k : ℕ) (g : ℕ → ℕ) :
    (arrOf N (fun t => if t < k then g t else 0)).set k (g k) =
      arrOf N (fun t => if t < k + 1 then g t else 0) := by
  rw [set_arrOf]
  refine arrOf_congr fun t _ => ?_
  by_cases h : t = k
  · simp [h]
  · simp only [if_neg h]
    by_cases h' : t < k
    · simp [h', show t < k + 1 by omega]
    · simp [h', show ¬ t < k + 1 by omega]

theorem psum_le (g : ℕ → ℕ) {c : ℕ} (hc : ∀ m, g m ≤ c) (k : ℕ) : psum g k ≤ k * c := by
  induction k with
  | zero => simp [psum]
  | succ k ih => rw [psum_succ, Nat.succ_mul]; have := hc k; omega

/-- The partial sums of the weighted completion times. -/
def totU (p w f : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ m ∈ Finset.range k, w (f m) * psum (fun t => p (f t)) (m + 1)

theorem totU_le (p w f : ℕ → ℕ) {c : ℕ} (hp : ∀ m, p m ≤ c) (hw : ∀ m, w m ≤ c) (k : ℕ) :
    totU p w f k ≤ k * (c * (k * c)) := by
  unfold totU
  calc ∑ m ∈ Finset.range k, w (f m) * psum (fun t => p (f t)) (m + 1)
      ≤ ∑ m ∈ Finset.range k, c * (k * c) := Finset.sum_le_sum fun m hm => by
        have h1 := psum_le (fun t => p (f t)) (fun t => hp (f t)) (m + 1)
        have h2 : (m + 1) * c ≤ k * c := Nat.mul_le_mul_right _ (by simp at hm; omega)
        exact Nat.mul_le_mul (hw _) (h1.trans h2)
    _ = k * (c * (k * c)) := by simp

/-- **The program**, on every word of the right shape: it writes `ansU u`. -/
theorem run_smith (u : List ℕ) (hsh : Shape u) :
    ∃ σ', Run (bndS u) smithCom (initEnv (fun _ => u.length + 2) (u.length :: u)) σ' (costS u) ∧
      σ'.out = ansU u := by
  set L := u.length with hL
  set M := Lax434175.Results.maxEntry u with hM
  set n := nU u with hn
  set B := bndS u with hB
  set N := L + 2 with hN
  have hBdef : B = 64 * (L + M + 2) ^ 4 := rfl
  have hK : 20 * (L + M + 2) < B := by
    have : (L + M + 2) * 1 ≤ (L + M + 2) * (L + M + 2) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
    rw [hBdef]; nlinarith
  have hK4 : (L + M + 2) ^ 4 + (L + M + 2) ^ 3 < B := by
    have : (L + M + 2) ^ 3 ≤ (L + M + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have : 0 < (L + M + 2) ^ 4 := by positivity
    rw [hBdef]; omega
  have hnL : n ≤ L := hsh.1
  have hidx := hsh.2
  have hgetM : ∀ j, u.getD j 0 ≤ M := fun j => getD_le_max u j
  have hnM : n ≤ M := hgetM 1
  have hMB : M < B := by omega
  have hLB : L + 2 < B := by omega
  -- the word
  obtain ⟨σ1, r1, ha1, hL1, ho1, hv1, harr1⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) hMB) hLB
  have hra : ∀ τ : Env, τ.arrs "a" = arrW u → ∀ {e : Expr} {k : ℕ}, e.evalB B τ = some k → k < N →
      (Expr.get "a" e).evalB B τ = some (u.getD k 0) := fun τ ha e k he hk =>
    ev_arr (f := fun j => u.getD j 0) (N := u.length + 2) ha he hk (lt_of_le_of_lt (hgetM k) hMB)
  -- n and q
  have r2 : Run B (.assign "n" (.get "a" (.lit 1))) σ1 (σ1.setVar "n" n) 3 :=
    (Run.assign (hra σ1 ha1 (evalB_lit (by omega)) (by omega))).mono (by simp)
  set σ2 := σ1.setVar "n" n with hσ2
  have r3 : Run B (.assign "q" (.add (.mul (.lit 15) (V "n")) (.lit 11))) σ2
      (σ2.setVar "q" (15 * n + 11)) 6 :=
    (Run.assign (evalB_bin (evalB_bin (evalB_lit (by omega)) (evalB_var (by simp [σ2]; omega))
      (by simp [σ2]; omega)) (evalB_lit (by omega)) (by simp [σ2]; omega))).mono (by simp)
      |>.congr (by simp [σ2])
  set σ3 := σ2.setVar "q" (15 * n + 11) with hσ3
  -- the fill loop
  let FI : ℕ → Env → Prop := fun k τ => τ.vars "j" = k ∧ τ.vars "n" = n ∧
    τ.vars "q" = 15 * n + 11 ∧ τ.vars "L" = L ∧ τ.arrs "a" = arrW u ∧
    τ.arrs "P" = arrOf N (fun t => if t < k then u.getD (15 * t + 5) 0 else 0) ∧
    τ.arrs "W" = arrOf N (fun t => if t < k then u.getD (15 * n + 11 + 3 * t) 0 else 0) ∧
    τ.arrs "A" = arrOf N (fun t => if t < k then t else 0) ∧
    τ.arrs "T" = arrOf N (fun _ => 0) ∧ τ.out = []
  have hz : ∀ b, b ≠ "a" → σ3.arrs b = arrOf N (fun t => if t < 0 then (0 : ℕ) else 0) := by
    intro b hb
    simp only [σ3, σ2, arrs_setVar, harr1 b hb, replicate_eq_arrOf]
    exact arrOf_congr fun t _ => by simp
  obtain ⟨σ4, r4, ⟨-, hn4, hq4, hL4, ha4, hP4, hW4, hA4, hT4, ho4⟩⟩ :=
    run_forLoop (B := B) "j" "n" fillBody n 23 (by omega) FI (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hj, hnτ, hq, hLτ, ha, hP, hW, hA, hT, ho⟩ => by
      have hi := hidx k hk
      have e1 : (Expr.get "a" (.add (.mul (.lit 15) (V "j")) (.lit 5))).evalB B τ =
          some (u.getD (15 * k + 5) 0) :=
        hra τ ha (ev_add (ev_mul (ev_lit (by omega)) (ev_var hj (by omega)) (by omega))
          (ev_lit (by omega)) (by omega)) (by omega)
      have s1 : Run B (.store "P" (V "j") (.get "a" (.add (.mul (.lit 15) (V "j")) (.lit 5)))) τ
          (τ.setArr "P" k (u.getD (15 * k + 5) 0)) 8 :=
        (Run.store (ev_var hj (by omega)) e1 (by rw [hP]; simp; omega)).mono (by simp)
      set τ1 := τ.setArr "P" k (u.getD (15 * k + 5) 0)
      have e2 : (Expr.get "a" (.add (V "q") (.mul (.lit 3) (V "j")))).evalB B τ1 =
          some (u.getD (15 * n + 11 + 3 * k) 0) :=
        hra τ1 (by simp [τ1, ha]) (ev_add (ev_var (by simp [τ1, hq]) (by omega))
          (ev_mul (ev_lit (by omega)) (ev_var (by simp [τ1, hj]) (by omega)) (by omega))
          (by omega)) (by omega)
      have s2 : Run B (.store "W" (V "j") (.get "a" (.add (V "q") (.mul (.lit 3) (V "j"))))) τ1
          (τ1.setArr "W" k (u.getD (15 * n + 11 + 3 * k) 0)) 8 :=
        (Run.store (ev_var (by simp [τ1, hj]) (by omega)) e2 (by simp [τ1, hW]; omega)).mono
          (by simp)
      set τ2 := τ1.setArr "W" k (u.getD (15 * n + 11 + 3 * k) 0)
      have s3 : Run B (.store "A" (V "j") (V "j")) τ2 (τ2.setArr "A" k k) 3 :=
        (Run.store (ev_var (by simp [τ2, τ1, hj]) (by omega)) (ev_var (by simp [τ2, τ1, hj]) (by omega))
          (by simp [τ2, τ1, hA]; omega)).mono (by simp)
      set τ3 := τ2.setArr "A" k k
      have s4 := run_incr (B := B) (σ := τ3) "j" (by simp [τ3, τ2, τ1]; omega)
      refine ⟨_, (s1.seq (s2.seq (s3.seq s4))).mono (by simp), by simp [τ3, τ2, τ1, hj],
        by simp [τ3, τ2, τ1, hnτ], by simp [τ3, τ2, τ1, hq], by simp [τ3, τ2, τ1, hLτ],
        by simp [τ3, τ2, τ1, ha], ?_, ?_, ?_, by simp [τ3, τ2, τ1, hT], by simp [τ3, τ2, τ1, ho]⟩
      · simp only [τ3, τ2, τ1, arrs_setVar, arrs_setArr]
        simp only [show ("P" : String) ≠ "A" by decide, show ("P" : String) ≠ "W" by decide,
          if_false, if_true, hP]
        exact set_prefix N k (fun t => u.getD (15 * t + 5) 0)
      · simp only [τ3, τ2, τ1, arrs_setVar, arrs_setArr]
        simp only [show ("W" : String) ≠ "A" by decide, show ("W" : String) ≠ "P" by decide,
          if_false, if_true, hW]
        exact set_prefix N k (fun t => u.getD (15 * n + 11 + 3 * t) 0)
      · simp only [τ3, τ2, τ1, arrs_setVar, arrs_setArr]
        simp only [show ("A" : String) ≠ "W" by decide, show ("A" : String) ≠ "P" by decide,
          if_false, if_true, hA]
        exact set_prefix N k (fun t => t))
    (σ := σ3) ⟨by simp, by simp [σ3, σ2], by simp [σ3], by simp [σ3, σ2, hL1, hL],
      by simp [σ3, σ2, ha1], by simp [hz "P" (by decide)], by simp [hz "W" (by decide)],
      by simp [hz "A" (by decide)],
      by simp only [arrs_setVar]; rw [hz "T" (by decide)]; exact arrOf_congr fun t _ => by simp,
      by simp [σ3, σ2, ho1]⟩

  -- the sort
  set pP : ℕ → ℕ := fun t => if t < n then u.getD (15 * t + 5) 0 else 0 with hpP
  set wP : ℕ → ℕ := fun t => if t < n then u.getD (15 * n + 11 + 3 * t) 0 else 0 with hwP
  have hpM : ∀ t, pP t ≤ M := fun t => by
    simp only [pP]; split_ifs
    · exact hgetM _
    · omega
  have hwM : ∀ t, wP t ≤ M := fun t => by
    simp only [wP]; split_ifs
    · exact hgetM _
    · omega
  have hKsq : (L + M + 2) * (L + M + 2) ≤ (L + M + 2) ^ 4 := by
    rw [show (L + M + 2) ^ 4 = (L + M + 2) * (L + M + 2) * ((L + M + 2) * (L + M + 2)) by ring]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hMM : M * M < B := by
    have : M * M ≤ (L + M + 2) * (L + M + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hc := cmpSmith_cmp (B := B) (N := N) (n := n) (p := pP) (w := wP) (by omega) (by omega)
    (fun a b _ _ => lt_of_le_of_lt (Nat.mul_le_mul (hpM a) (hwM b)) hMM)
    (fun a _ => lt_of_le_of_lt (hpM a) hMB) (fun a _ => lt_of_le_of_lt (hwM a) hMB)
  obtain ⟨σ5, f, r5, hA5, hperm, hsort, hctx5⟩ := run_msort hc (by omega) (by omega) hn4 hA4 hT4
    (fun t ht => by simp [ht]) ⟨hP4, hW4⟩
  have hn5 : σ5.vars "n" = n := by rw [r5.frame_var "n" (by decide), hn4]
  have hL5 : σ5.vars "L" = L := by rw [r5.frame_var "L" (by decide), hL4]
  have ha5 : σ5.arrs "a" = arrW u := by rw [r5.frame_arr "a" (by decide), ha4]
  have ho5 : σ5.out = [] := by rw [r5.out_eq (by decide), ho4]
  have hseg0 : seg (fun t => if t < n then t else 0) 0 n = List.range n :=
    List.ext_getElem (by simp) fun t h1 h2 => by simp at h1; simp [getElem_seg, h1]
  have hperm' : (seg f 0 n).Perm (List.range n) := hseg0 ▸ hperm
  have hfn : ∀ t < n, f t < n := fun t ht => by
    have hm : f t ∈ seg f 0 n := by
      unfold seg; exact List.mem_map.mpr ⟨t, by simpa using ht, by simp⟩
    simpa using hperm'.mem_iff.mp hm
  -- the sum
  have r6 : Run B (.assign "tm" (.lit 0)) σ5 (σ5.setVar "tm" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have r7 : Run B (.assign "tot" (.lit 0)) (σ5.setVar "tm" 0) ((σ5.setVar "tm" 0).setVar "tot" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ7 := (σ5.setVar "tm" 0).setVar "tot" 0 with hσ7
  let SI : ℕ → Env → Prop := fun k τ => τ.vars "j" = k ∧ τ.vars "n" = n ∧ τ.vars "L" = L ∧
    τ.arrs "a" = arrW u ∧ τ.arrs "P" = arrOf N pP ∧ τ.arrs "W" = arrOf N wP ∧
    τ.arrs "A" = arrOf N f ∧ τ.vars "tm" = psum (fun m => pP (f m)) k ∧
    τ.vars "tot" = totU pP wP f k ∧ τ.out = []
  have hKn : n * M ≤ (L + M + 2) * (L + M + 2) := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨σ8, r8, ⟨-, -, hL8, ha8, -, -, -, -, htot8, ho8⟩⟩ :=
    run_forLoop (B := B) "j" "n" sumBody n 19 (by omega) SI (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hj, hnτ, hLτ, ha, hP, hW, hA, htm, htot, ho⟩ => by
      have hfk := hfn k hk
      have s1 : Run B (.assign "x" (.get "A" (V "j"))) τ (τ.setVar "x" (f k)) 3 :=
        (Run.assign (ev_arr (N := N) (f := f) (k := k) hA (ev_var hj (by omega)) (by omega)
          (by omega))).mono (by simp)
      set τ1 := τ.setVar "x" (f k)
      have hps : psum (fun m => pP (f m)) (k + 1) ≤ (L + M + 2) * (L + M + 2) := by
        have := psum_le (fun m => pP (f m)) (fun m => hpM (f m)) (k + 1)
        have : (k + 1) * M ≤ n * M := Nat.mul_le_mul_right _ (by omega)
        omega
      have hsucc := psum_succ (fun m => pP (f m)) k
      have s2 : Run B (.assign "tm" (.add (V "tm") (.get "P" (V "x")))) τ1
          (τ1.setVar "tm" (psum (fun m => pP (f m)) (k + 1))) 5 := by
        have := Run.assign (B := B) (σ := τ1) (x := "tm") (ev_add
          (ev_var (x := "tm") (v := psum (fun m => pP (f m)) k) (by simp [τ1, htm]) (by omega))
          (ev_arr (a := "P") (N := N) (f := pP) (k := f k) (by simp [τ1, hP])
            (ev_var (x := "x") (v := f k) (by simp [τ1]) (by omega)) (by omega)
            (lt_of_le_of_lt (hpM _) hMB)) (by omega))
        rw [← hsucc] at this
        exact this.mono (by simp)
      set τ2 := τ1.setVar "tm" (psum (fun m => pP (f m)) (k + 1))
      have hwt : wP (f k) * psum (fun m => pP (f m)) (k + 1) ≤ (L + M + 2) ^ 3 := by
        have := Nat.mul_le_mul (hwM (f k)) hps
        have : M * ((L + M + 2) * (L + M + 2)) ≤ (L + M + 2) ^ 3 := by
          rw [show (L + M + 2) ^ 3 = (L + M + 2) * ((L + M + 2) * (L + M + 2)) by ring]
          exact Nat.mul_le_mul_right _ (by omega)
        omega
      have htotb : totU pP wP f k ≤ (L + M + 2) ^ 4 := by
        have := totU_le pP wP f hpM hwM k
        have h1 : k * (M * (k * M)) ≤ (L + M + 2) * ((L + M + 2) * (L + M + 2)) * (L + M + 2) := by
          have e : k * (M * (k * M)) = (k * M) * (k * M) := by ring
          have hkM : k * M ≤ (L + M + 2) * (L + M + 2) := (Nat.mul_le_mul_right _ hk.le).trans hKn
          rw [e]
          calc (k * M) * (k * M) ≤ ((L + M + 2) * (L + M + 2)) * ((L + M + 2) * (L + M + 2)) :=
                Nat.mul_le_mul hkM hkM
            _ = (L + M + 2) * ((L + M + 2) * (L + M + 2)) * (L + M + 2) := by ring
        have h2 : (L + M + 2) * ((L + M + 2) * (L + M + 2)) * (L + M + 2) = (L + M + 2) ^ 4 := by ring
        omega
      have hsucc2 : totU pP wP f (k + 1) =
          totU pP wP f k + wP (f k) * psum (fun m => pP (f m)) (k + 1) := by
        simp [totU, Finset.sum_range_succ]
      have s3 : Run B (.assign "tot" (.add (V "tot") (.mul (.get "W" (V "x")) (V "tm")))) τ2
          (τ2.setVar "tot" (totU pP wP f (k + 1))) 7 := by
        have := Run.assign (B := B) (σ := τ2) (x := "tot") (ev_add
          (ev_var (x := "tot") (v := totU pP wP f k) (by simp [τ2, τ1, htot]) (by omega))
          (ev_mul (ev_arr (a := "W") (N := N) (f := wP) (k := f k) (by simp [τ2, τ1, hW])
            (ev_var (x := "x") (v := f k) (by simp [τ2, τ1]) (by omega)) (by omega)
            (lt_of_le_of_lt (hwM _) hMB))
            (ev_var (x := "tm") (v := psum (fun m => pP (f m)) (k + 1)) (by simp [τ2]) (by omega))
            (by omega)) (by omega))
        rw [← hsucc2] at this
        exact this.mono (by simp)
      set τ3 := τ2.setVar "tot" (totU pP wP f (k + 1))
      have s4 := run_incr (B := B) (σ := τ3) "j" (by simp [τ3, τ2, τ1, hj]; omega)
      refine ⟨_, (s1.seq (s2.seq (s3.seq s4))).mono (by simp), by simp [τ3, τ2, τ1, hj],
        by simp [τ3, τ2, τ1, hnτ], by simp [τ3, τ2, τ1, hLτ], by simp [τ3, τ2, τ1, ha],
        by simp [τ3, τ2, τ1, hP], by simp [τ3, τ2, τ1, hW], by simp [τ3, τ2, τ1, hA],
        by simp [τ3, τ2, τ1], by simp [τ3, τ2, τ1], by simp [τ3, τ2, τ1, ho]⟩)
    (σ := σ7) ⟨by simp, by simp [σ7, hn5], by simp [σ7, hL5], by simp [σ7, ha5],
      by simp [σ7, hctx5.1], by simp [σ7, hctx5.2], by simp [σ7, hA5], by simp [σ7, psum],
      by simp [σ7, totU], by simp [σ7, ho5]⟩
  -- the threshold
  have r9 : Run B (.assign "s" (.get "a" (.sub (V "L") (.lit 2)))) σ8
      (σ8.setVar "s" (u.getD (L - 2) 0)) 5 :=
    (Run.assign (hra σ8 ha8 (ev_sub (ev_var hL8 (by omega)) (ev_lit (by omega))) (by omega))).mono
      (by simp)
  set σ9 := σ8.setVar "s" (u.getD (L - 2) 0)
  have r10 : Run B (.assign "d" (.get "a" (.sub (V "L") (.lit 1)))) σ9
      (σ9.setVar "d" (u.getD (L - 1) 0)) 5 :=
    (Run.assign (hra σ9 (by simp [σ9, ha8]) (ev_sub (ev_var (by simp [σ9, hL8]) (by omega))
      (ev_lit (by omega))) (by omega))).mono (by simp)
  set σ10 := σ9.setVar "d" (u.getD (L - 1) 0)
  have htot : totU pP wP f n = opt (pU u) (wU u) (nU u) :=
    seqCost_eq_opt pP wP f n hperm' hsort
  have hsB : u.getD (L - 2) 0 < B := lt_of_le_of_lt (hgetM _) hMB
  have hdB : u.getD (L - 1) 0 < B := lt_of_le_of_lt (hgetM _) hMB
  have htotB : totU pP wP f n < B := by
    have := totU_le pP wP f hpM hwM n
    have h1 : n * (M * (n * M)) ≤ (L + M + 2) ^ 4 := by
      have e : n * (M * (n * M)) = (n * M) * (n * M) := by ring
      rw [e, show (L + M + 2) ^ 4 = ((L + M + 2) * (L + M + 2)) * ((L + M + 2) * (L + M + 2)) by ring]
      exact Nat.mul_le_mul hKn hKn
    omega
  have hcs := evalB_condEq (B := B) (σ := σ10) (ev_var (x := "s") (by simp [σ10, σ9]) hsB)
    (ev_lit (n := 0) (by omega))
  have hcd := evalB_condLt (B := B) (σ := σ10) (ev_var (x := "d") (by simp [σ10]) hdB)
    (ev_var (x := "tot") (by simp [σ10, σ9, htot8]) htotB)
  have l0 : (Expr.lit 0).evalB B σ10 = some 0 := evalB_lit (by omega)
  have l1 : (Expr.lit 1).evalB B σ10 = some 1 := evalB_lit (by omega)
  have hfin : ∃ σ11, Run B (.ite (.eq (V "s") (.lit 0))
      (.ite (.lt (V "d") (V "tot")) (.write (.lit 0)) (.write (.lit 1))) (.write (.lit 0))) σ10 σ11 10 ∧
      σ11.out = ansU u := by
    have hans : ansU u = [if u.getD (L - 2) 0 = 0 ∧ totU pP wP f n ≤ u.getD (L - 1) 0 then 1 else 0] := by
      unfold ansU; rw [htot]
    have ho10 : σ10.out = [] := ho8
    by_cases h1 : u.getD (L - 2) 0 = 0
    · have c1 : (Cond.eq (V "s") (.lit 0)).evalB B σ10 = some true := by rw [hcs, h1]; rfl
      by_cases h2 : u.getD (L - 1) 0 < totU pP wP f n
      · have c2 : (Cond.lt (V "d") (V "tot")).evalB B σ10 = some true := by
          rw [hcd, decide_eq_true h2]
        refine ⟨_, (Run.ite_true c1 (Run.ite_true c2 (Run.write l0))).mono (by simp), ?_⟩
        rw [hans, if_neg (by omega)]
        show σ10.out ++ [0] = [0]
        rw [ho10]; rfl
      · have c2 : (Cond.lt (V "d") (V "tot")).evalB B σ10 = some false := by
          rw [hcd, decide_eq_false h2]
        refine ⟨_, (Run.ite_true c1 (Run.ite_false c2 (Run.write l1))).mono (by simp), ?_⟩
        rw [hans, if_pos ⟨h1, by omega⟩]
        show σ10.out ++ [1] = [1]
        rw [ho10]; rfl
    · have c1 : (Cond.eq (V "s") (.lit 0)).evalB B σ10 = some false := by
        rw [hcs, beq_false_of_ne h1]
      refine ⟨_, (Run.ite_false c1 (Run.write l0)).mono (by simp), ?_⟩
      rw [hans, if_neg (fun h => h1 h.1)]
      show σ10.out ++ [0] = [0]
      rw [ho10]; rfl
  obtain ⟨σ11, r11, ho11⟩ := hfin
  refine ⟨σ11, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    (r10.seq r11)))))))))).mono ?_, ho11⟩
  simp only [costS, ← hL, ← hn]
  omega

end SmithProgram

/-! ### The semantics of `1||ΣwjCj` -/

open Lax434175 Lax434175.Problems Lax434175.Assembly

section Order
variable {n : ℕ}

/-- The total weighted completion time of jobs run without idle time, through the set of
the jobs before each job. -/
theorem sum_start (F : Fin n → Finset (Fin n)) (pp w : Fin n → ℕ) :
    ∑ j, w j * (∑ i ∈ F j, pp i + pp j) =
      ∑ j, w j * pp j + ∑ i, ∑ j, if i ∈ F j then pp i * w j else 0 := by
  have h : ∀ j, w j * (∑ i ∈ F j, pp i + pp j) =
      w j * pp j + ∑ i, if i ∈ F j then pp i * w j else 0 := by
    intro j
    rw [mul_add, add_comm, Finset.mul_sum]
    congr 1
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, Finset.sum_comm]

end Order

section Single
variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1)

/-- The schedule that runs the jobs without idle time from `0` in an order `S`. -/
def orderStart (S : Fin X.jobs → Fin X.jobs → Prop) [DecidableRel S] (j : Fin X.jobs) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => S i j), PreemptionUseless.dur hs i

/-- The piece of a job. -/
def orderPiece (S : Fin X.jobs → Fin X.jobs → Prop) [DecidableRel S] (j : Fin X.jobs) :
    Operations.Piece X :=
  ⟨PreemptionUseless.opOf hs j, Finset.univ, (orderStart hs S j : NNRat),
    (PreemptionUseless.dur hs j : NNRat)⟩

/-- The schedule in the order `S`. -/
def orderSched (S : Fin X.jobs → Fin X.jobs → Prop) [DecidableRel S] : Operations.Sched X :=
  ⟨List.ofFn (orderPiece hs S)⟩

variable (S : Fin X.jobs → Fin X.jobs → Prop) [DecidableRel S]

theorem piecesOf_order (o : Operations.Op X) :
    Operations.piecesOf (orderSched hs S) o = [orderPiece hs S o.1] := by
  unfold Operations.piecesOf orderSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Operations.Piece X => decide (q.op = o)) ∘ orderPiece hs S) =
      fun i => decide (i = o.1) := by
    funext i
    simp only [Function.comp, orderPiece]
    apply decide_eq_decide.mpr
    constructor
    · rintro rfl; rfl
    · rintro rfl; exact PreemptionUseless.opOf_eq hs o
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem piecesOfJob_order (j : Fin X.jobs) :
    Operations.piecesOfJob (orderSched hs S) j = [orderPiece hs S j] := by
  unfold Operations.piecesOfJob orderSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Operations.Piece X => decide (q.op.1 = j)) ∘ orderPiece hs S) =
      fun i => decide (i = j) := rfl
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem completion_order (j : Fin X.jobs) :
    Operations.kernel.completion X (orderSched hs S) j =
      ((orderStart hs S j + PreemptionUseless.dur hs j : ℕ) : NNRat) := by
  change (((Operations.piecesOfJob (orderSched hs S) j).map Operations.Piece.finish).max?).getD 0 = _
  rw [piecesOfJob_order]
  change (orderStart hs S j : NNRat) + (PreemptionUseless.dur hs j : NNRat) = _
  push_cast
  rfl

theorem orderStart_le (hirr : ∀ i, ¬ S i i) (htr : ∀ a b c, S a b → S b c → S a c) {i j : Fin X.jobs}
    (h : S i j) : orderStart hs S i + PreemptionUseless.dur hs i ≤ orderStart hs S j := by
  unfold orderStart
  have hi : i ∉ Finset.univ.filter (fun k => S k i) := by simp [hirr]
  rw [add_comm, ← Finset.sum_insert hi]
  refine Finset.sum_le_sum_of_subset fun k hk => ?_
  rcases Finset.mem_insert.mp hk with rfl | hk
  · simpa using h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact htr _ _ _ hk h

theorem order_feasible (hm : 0 < X.machines) (hirr : ∀ i, ¬ S i i)
    (htr : ∀ a b c, S a b → S b c → S a c) (htot : ∀ i j, i ≠ j → S i j ∨ S j i) :
    Operations.feasible (orderSched hs S) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  · refine List.pairwise_ofFn.mpr fun i j hij _ => ?_
    rcases htot i j (ne_of_lt hij) with h | h
    · left
      change (orderStart hs S i : NNRat) + (PreemptionUseless.dur hs i : NNRat) ≤
        (orderStart hs S j : NNRat)
      exact_mod_cast orderStart_le hs S hirr htr h
    · right
      change (orderStart hs S j : NNRat) + (PreemptionUseless.dur hs j : NNRat) ≤
        (orderStart hs S i : NNRat)
      exact_mod_cast orderStart_le hs S hirr htr h

theorem order_holds : Operations.holds .none X (orderSched hs S) := fun o =>
  ⟨orderPiece hs S o.1, piecesOf_order hs S o, by
    change (PreemptionUseless.dur hs o.1 : NNRat) = _
    unfold PreemptionUseless.dur
    rw [PreemptionUseless.opOf_eq hs]
    rfl, orderStart hs S o.1, rfl⟩

end Single

section Instance
open Lax434175.Sanity
variable (x : Inst OperationsFamily.family singleWC)

theorem ops_eq (j : Fin x.base.jobs) : x.base.ops j = 1 := x.admitted .jobStructure j

theorem machines_eq : x.base.machines = 1 := by
  obtain ⟨h1, h2⟩ := x.admitted .machineCount
  exact le_antisymm h1 (h2 1 rfl)

theorem release_eq (j : Fin x.base.jobs) : x.base.r j = 0 := x.admitted .releaseDates j

/-- The processing time of job `j`, `0` past the last job. -/
def pOf (j : ℕ) : ℕ :=
  if h : j < x.base.jobs then
    x.base.p ⟨j, h⟩ ⟨0, by rw [ops_eq]; omega⟩ ⟨0, by rw [machines_eq]; omega⟩
  else 0

/-- The weight of job `j`, `0` past the last job. -/
def wOf (j : ℕ) : ℕ :=
  if h : j < x.base.jobs then ResultParameters.Ops.weight singleWC x ⟨j, h⟩ else 0

theorem dur_eq (j : Fin x.base.jobs) : PreemptionUseless.dur (ops_eq x) j = pOf x j := by
  have hm := machines_eq x
  unfold PreemptionUseless.dur Operations.duration pOf
  rw [dif_pos j.isLt]
  have huniv : (Finset.univ : Finset (Fin x.base.machines)) = {⟨0, by omega⟩} := by
    ext i; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Fin.ext (by have := i.isLt; omega)
  rw [huniv, Finset.sup_singleton]
  rfl

theorem cost_eq (σ : Operations.Sched x.base) : (problem _ singleWC).cost x σ =
    ((∑ j : Fin x.base.jobs, (wOf x j : NNRat) * Operations.kernel.completion x.base σ j :
      NNRat) : ℚ) := by
  show ((∑ j, (Objectives.weight Objectives.Value.sumWC x.objectiveData j : NNRat) *
    (Operations.kernel.completion x.base σ j -
      ((Objectives.dueDate Objectives.Value.sumWC x.objectiveData j : ℕ) : NNRat)) : NNRat) : ℚ) = _
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : wOf x j = Objectives.weight Objectives.Value.sumWC x.objectiveData j := by
    unfold wOf
    split_ifs with h
    · rfl
    · exact absurd j.isLt h
  rw [hw]
  change _ * (_ - ((0 : ℕ) : NNRat)) = _
  simp

/-- **Every schedule pays at least `opt`.** -/
theorem opt_le (σ : Operations.Sched x.base) (hσ : (problem _ singleWC).feasible x σ) :
    (opt (pOf x) (wOf x) x.base.jobs : ℚ) ≤ (problem _ singleWC).cost x σ := by
  have hs := ops_eq x
  have hk : Operations.feasible σ := hσ.1
  have hm : Operations.holds .pmtn x.base σ :=
    PreemptionUseless.holds_pmtn_of_none σ (hσ.2 .interruption)
  have hM : x.base.machines ≤ 1 := (machines_eq x).le
  rw [cost_eq]
  have step1 : ((∑ j : Fin x.base.jobs, wOf x j * (∑ i ∈ PreemptionUseless.befores σ j,
      pOf x i + pOf x j) : ℕ) : NNRat) ≤
      ∑ j : Fin x.base.jobs, (wOf x j : NNRat) * Operations.kernel.completion x.base σ j := by
    push_cast
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ zero_le
    have := PreemptionUseless.capacity hs hk hm hM j
    unfold PreemptionUseless.newStart at this
    simp only [dur_eq] at this
    exact_mod_cast this
  rw [sum_start] at step1
  have step2 := pairs_ge (fun i j => i ∈ PreemptionUseless.befores σ j)
    (fun i j => pOf x i * wOf x j)
    (fun i h => PreemptionUseless.before_irrefl σ i (by simpa [PreemptionUseless.befores] using h))
    (fun i j h => by
      rcases PreemptionUseless.before_total σ h with h' | h'
      · exact Or.inl (by simpa [PreemptionUseless.befores] using h')
      · exact Or.inr (by simpa [PreemptionUseless.befores] using h'))
  have : opt (pOf x) (wOf x) x.base.jobs ≤ ∑ j : Fin x.base.jobs, wOf x j * pOf x j +
      ∑ i : Fin x.base.jobs, ∑ j : Fin x.base.jobs,
        if i ∈ PreemptionUseless.befores σ j then pOf x i * wOf x j else 0 := by
    unfold opt; omega
  have h3 : ((opt (pOf x) (wOf x) x.base.jobs : ℕ) : NNRat) ≤
      ∑ j : Fin x.base.jobs, (wOf x j : NNRat) * Operations.kernel.completion x.base σ j :=
    le_trans (by exact_mod_cast this) step1
  exact_mod_cast h3

/-- Smith's order of the jobs, ties broken by number. -/
def smithOrder (i j : Fin x.base.jobs) : Prop :=
  smithLe (pOf x) (wOf x) i j = true ∧ (smithLe (pOf x) (wOf x) j i = false ∨ i < j)

instance : DecidableRel (smithOrder x) := fun _ _ => by unfold smithOrder; infer_instance

theorem smithOrder_irrefl (i : Fin x.base.jobs) : ¬ smithOrder x i i := by
  rintro ⟨h1, h2 | h2⟩
  · rw [h1] at h2; exact Bool.noConfusion h2
  · exact lt_irrefl _ h2

theorem smithOrder_total (i j : Fin x.base.jobs) (h : i ≠ j) : smithOrder x i j ∨ smithOrder x j i := by
  have ht := smithLe_total (pOf x) (wOf x) i j
  unfold smithOrder
  rcases lt_or_gt_of_ne h with hij | hij <;>
  cases h1 : smithLe (pOf x) (wOf x) i j <;> cases h2 : smithLe (pOf x) (wOf x) j i <;>
    simp_all

theorem smithOrder_asymm (i j : Fin x.base.jobs) (h : smithOrder x i j) : ¬ smithOrder x j i := by
  rintro ⟨h3, h4⟩
  obtain ⟨h1, h2⟩ := h
  rcases h2 with h2 | h2
  · rw [h3] at h2; exact Bool.noConfusion h2
  · rcases h4 with h4 | h4
    · rw [h1] at h4; exact Bool.noConfusion h4
    · exact lt_asymm h2 h4

theorem smithOrder_trans (a b c : Fin x.base.jobs) (hab : smithOrder x a b) (hbc : smithOrder x b c) :
    smithOrder x a c := by
  obtain ⟨h1, h2⟩ := hab
  obtain ⟨h3, h4⟩ := hbc
  have hac := smithLe_trans (pOf x) (wOf x) _ _ _ h1 h3
  refine ⟨hac, ?_⟩
  cases hca : smithLe (pOf x) (wOf x) c a
  · exact Or.inl rfl
  · right
    have hcb := smithLe_trans (pOf x) (wOf x) _ _ _ hca h1
    have hba := smithLe_trans (pOf x) (wOf x) _ _ _ h3 hca
    rcases h2 with h2 | h2
    · rw [hba] at h2; exact Bool.noConfusion h2
    · rcases h4 with h4 | h4
      · rw [hcb] at h4; exact Bool.noConfusion h4
      · exact lt_trans h2 h4

/-- **Smith's schedule.** -/
noncomputable def smithSched : Operations.Sched x.base := orderSched (ops_eq x) (smithOrder x)

theorem smith_feasible : (problem _ singleWC).feasible x (smithSched x) := by
  have hs := ops_eq x
  refine ⟨order_feasible hs _ (by rw [machines_eq]; omega) (smithOrder_irrefl x)
    (smithOrder_trans x) (smithOrder_total x), fun i => ?_⟩
  cases i
  · exact order_holds hs _
  · exact TimeReversal.ordered_single .single rfl x.base (smithSched x)
  · trivial
  · trivial
  · trivial
  · trivial
  · intro q hq
    change (q.machines).card = 1
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    change (Finset.univ : Finset (Fin x.base.machines)).card = 1
    rw [Finset.card_univ, Fintype.card_fin, machines_eq]
  · exact TimeReversal.release_zero _ x.base (release_eq x) _
  · exact fun _ => trivial
  · exact fun _ _ h => h.elim
  · exact TimeReversal.delays_none .none rfl _ _ _
  · exact TimeReversal.server_none .none rfl _ _ _
  · exact TimeReversal.forbidden_none .none rfl _ _ _
  · trivial
  · intro h; cases h
  · exact TimeReversal.transport_none .none rfl x.base _ (x.admitted .transportation) _
  · exact TimeReversal.idle_none .none rfl _ _
  · exact TimeReversal.setups_none .none rfl _ _ _

theorem smith_cost :
    (problem _ singleWC).cost x (smithSched x) = (opt (pOf x) (wOf x) x.base.jobs : ℚ) := by
  rw [cost_eq]
  have hs := ops_eq x
  have hc : ∀ j, Operations.kernel.completion x.base (smithSched x) j =
      ((orderStart hs (smithOrder x) j + PreemptionUseless.dur hs j : ℕ) : NNRat) := fun j =>
    completion_order hs (smithOrder x) j
  have e : ∑ j : Fin x.base.jobs,
      (wOf x j : NNRat) * Operations.kernel.completion x.base (smithSched x) j =
      ((∑ j : Fin x.base.jobs, wOf x j * (∑ i ∈ Finset.univ.filter (fun i => smithOrder x i j),
        pOf x i + pOf x j) : ℕ) : NNRat) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j]
    unfold orderStart
    simp only [dur_eq]
    push_cast
    rfl
  have hmem : ∀ i j, i ∈ Finset.univ.filter (fun i => smithOrder x i j) ↔ smithOrder x i j := by
    intro i j; simp
  rw [e, sum_start, pairs_eq (fun i j => i ∈ Finset.univ.filter (fun i => smithOrder x i j))
    (fun i j => pOf x i * wOf x j) (fun i h => smithOrder_irrefl x i ((hmem i i).mp h))
    (fun i j h => by
      rcases smithOrder_total x i j h with h' | h'
      · exact Or.inl ((hmem i j).mpr h')
      · exact Or.inr ((hmem j i).mpr h'))
    (fun i j h h' => smithOrder_asymm x i j ((hmem i j).mp h) ((hmem j i).mp h'))
    (fun i j h => smithLe_mul _ _ ((hmem i j).mp h).1)]
  rfl

/-- **The answer of an instance of `1||ΣwjCj`.** -/
theorem decides_iff (D : ℚ) :
    (problem _ singleWC).Decides x D ↔ (opt (pOf x) (wOf x) x.base.jobs : ℚ) ≤ D := by
  constructor
  · rintro ⟨σ, hσ, hc⟩
    exact (opt_le x σ hσ).trans hc
  · intro h
    exact ⟨smithSched x, smith_feasible x, (smith_cost x).trans_le h⟩

end Instance

/-! ### The standard words of `1||ΣwjCj` -/

section Words
open Lax434175.Sanity Lax434175.StandardReading Lax434175.Results

/-- The record of a job with processing time `p`, preceded by its length: one operation, its
time on the one machine, no deadline, the machine block `{(0, 0)}`, no setup, the transport
block `{(0, 0, 0)}` and batch `0`. -/
def recW (p : ℕ) : List ℕ := [14, 1, p, 0, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0]

/-- The standard word of an instance of `1||ΣwjCj` with `n` jobs, processing times `p` and
weights `w`. -/
def stdInst (n : ℕ) (p w : ℕ → ℕ) : List ℕ :=
  [0, n, 1] ++ (List.ofFn fun j : Fin n => recW (p j)).flatten ++ [0] ++
    (if n = 0 then [0] else [1, 4, 1, 0, 0, 0]) ++ (List.ofFn fun j : Fin n => [0, w j, 0]).flatten

variable (x : Inst OperationsFamily.family singleWC)

theorem ofFn_eq_single {m : ℕ} (h : m = 1) (f : Fin m → ℕ) : List.ofFn f = [f ⟨0, by omega⟩] := by
  subst h; rfl

theorem jobHead_eq (j : Fin x.base.jobs) : jobHead x j = [1, pOf x j, 0] := by
  unfold jobHead
  rw [Lax434175Proofs.P200Words.flatten_ofFn_one (ops_eq x j), ofFn_eq_single (machines_eq x)]
  have h1 : [x.base.ops j] = [1] := by rw [ops_eq x j]
  rw [h1]
  simp only [pOf, dif_pos j.isLt]
  rfl

theorem machineTuples_eq (j : Fin x.base.jobs) : machineTuples x j = {[0, 0]} := by
  have hm := machines_eq x
  ext t
  simp only [machineTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, S, hv, rfl⟩
    have hk : k.val = 0 := by have := k.isLt; have := ops_eq x j; omega
    have hS : S = {⟨0, by omega⟩} := by
      have hc : S.card = 1 := hv
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      congr 1; exact Fin.ext (by have := i.isLt; omega)
    rw [hk, hS, Lax434175Proofs.IsemStandard.machinesWord_singleton]
  · rintro rfl
    refine ⟨⟨0, by rw [ops_eq]; omega⟩, {⟨0, by omega⟩}, Finset.card_singleton _, ?_⟩
    rw [Lax434175Proofs.IsemStandard.machinesWord_singleton]

theorem serverTuples_eq (j : Fin x.base.jobs) : serverTuples x j = ∅ := by
  ext t
  simp only [serverTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, f, hf, -⟩
  cases hf

theorem transportTuples_eq (j : Fin x.base.jobs) : transportTuples x j = {[0, 0, 0]} := by
  have h0 : ∀ k : Fin (x.base.ops j), k = ⟨0, by rw [ops_eq]; omega⟩ := fun k =>
    Fin.ext (by have := k.isLt; have := ops_eq x j; simp; omega)
  ext t
  simp only [transportTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, k', rfl⟩
    rw [h0 k, h0 k', show (x.data .transportation : Transportation.Data x.base.toShop).1 j _ _ = 0 from
      (x.admitted .transportation).1 j _ _]
  · rintro rfl
    exact ⟨⟨0, by rw [ops_eq]; omega⟩, ⟨0, by rw [ops_eq]; omega⟩, by
      rw [show (x.data .transportation : Transportation.Data x.base.toShop).1 j _ _ = 0 from
        (x.admitted .transportation).1 j _ _]⟩

theorem record (j : Fin x.base.jobs) :
    Record x j [1, pOf x j, 0, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0] := by
  refine ⟨flat [[0, 0]], [0], flat [[0, 0, 0]],
    machineTuples_eq x j ▸ Lax434175Proofs.IsemStandard.block_single _,
    serverTuples_eq x j ▸ Lax434175Proofs.IsemStandard.block_empty,
    transportTuples_eq x j ▸ Lax434175Proofs.IsemStandard.block_single _, ?_⟩
  rw [jobHead_eq]
  rfl

theorem pairTuples_eq : pairTuples x = ∅ := by
  ext t
  simp only [pairTuples, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ((⟨i, j, h, -⟩ | ⟨i, j, h, -⟩) | ⟨i, j, c, h, -⟩) <;> exact h

theorem globalTuples_eq : globalTuples x = if x.base.jobs = 0 then ∅ else {[1, 0, 0, 0]} := by
  ext t
  simp only [globalTuples, Set.mem_union, Set.mem_ofPred_eq]
  split_ifs with hn
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ((⟨τ, hτ, -⟩ | ⟨i, -, -⟩) | ⟨hr, -⟩)
    · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
    · exact absurd i.isLt (by omega)
    · exact absurd hr (by decide)
  · simp only [Set.mem_singleton_iff]
    constructor
    · rintro ((⟨τ, hτ, -⟩ | ⟨i, j, rfl⟩) | ⟨hr, -⟩)
      · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
      · rfl
      · exact absurd hr (by decide)
    · rintro rfl
      exact Or.inl (Or.inr ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩)

theorem global_block :
    Block (globalTuples x) (if x.base.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) := by
  rw [globalTuples_eq]
  split_ifs
  · exact Lax434175Proofs.IsemStandard.block_empty
  · exact Lax434175Proofs.IsemStandard.block_single _

theorem objWord_eq : objWord x = (List.ofFn fun j : Fin x.base.jobs => [0, wOf x j, 0]).flatten := by
  unfold objWord
  congr 1
  refine List.ofFn_inj.mpr (funext fun j => ?_)
  simp only [objOf, release_eq x j, wOf, dif_pos j.isLt]
  rfl

/-- **Every instance is written by the word of its data.** -/
theorem encodesOps : EncodesOps x (stdInst x.base.jobs (pOf x) (wOf x)) := by
  refine ⟨[0], _, pairTuples_eq x ▸ Lax434175Proofs.IsemStandard.block_empty, global_block x,
    Or.inl ⟨rfl, _, ⟨fun j => [1, pOf x j, 0, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0], record x, rfl⟩,
      ?_⟩⟩
  rw [objWord_eq, machines_eq]
  rfl

/-- **The word of an instance with its threshold.** -/
theorem word_eq {u : List ℕ} {D : ℤ} (h : EncodesDecision (StandardReading.ops.at singleWC) u x D) :
    u = stdInst x.base.jobs (pOf x) (wOf x) ++ int D := by
  obtain ⟨z, rfl, hz⟩ := h
  rw [Lax434175Proofs.P200Words.encodesOps_unique (s := singleWC) rfl x hz (encodesOps x)]
  rfl

end Words

/-! ### Reading the standard words -/

section WordReading
open Lax434175.StandardReading

theorem getD_append_length (l l' : List ℕ) (i : ℕ) : (l ++ l').getD (l.length + i) 0 = l'.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem getD_flatten_ofFn : ∀ {n : ℕ} (g : Fin n → List ℕ) (c : ℕ) (_ : ∀ j, (g j).length = c)
    (j : Fin n) (t : ℕ) (_ : t < c), (List.ofFn g).flatten.getD (c * j + t) 0 = (g j).getD t 0
  | 0, _, _, _, j, _, _ => j.elim0
  | n + 1, g, c, hg, j, t, ht => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [Fin.val_zero, mul_zero, zero_add]
      exact getD_append_lt (by rw [hg]; exact ht)
    · rw [Fin.val_succ, show c * (j' + 1) + t = (g 0).length + (c * j' + t) by rw [hg]; ring,
        getD_append_length]
      exact getD_flatten_ofFn (fun i => g i.succ) c (fun i => hg _) j' t ht

theorem length_flatten_ofFn : ∀ {n : ℕ} (g : Fin n → List ℕ) (c : ℕ) (_ : ∀ j, (g j).length = c),
    (List.ofFn g).flatten.length = c * n
  | 0, _, _, _ => by simp
  | n + 1, g, c, hg => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hg,
      length_flatten_ofFn (fun i => g i.succ) c (fun i => hg _)]
    ring

variable (n : ℕ) (p w : ℕ → ℕ) (D : ℤ)

theorem length_stdInst : (stdInst n p w).length = 3 + 15 * n + 1 + (if n = 0 then 1 else 6) + 3 * n := by
  unfold stdInst
  simp only [List.length_append, length_flatten_ofFn (fun j : Fin n => recW (p j)) 15 (fun _ => rfl),
    length_flatten_ofFn (fun j : Fin n => [0, w j, 0]) 3 (fun _ => rfl)]
  split_ifs <;> simp only [List.length_cons, List.length_nil]

theorem nU_std : nU (stdInst n p w ++ int D) = n := by
  simp [nU, stdInst]

theorem getD_p {j : ℕ} (hj : j < n) : (stdInst n p w ++ int D).getD (15 * j + 5) 0 = p j := by
  unfold stdInst
  simp only [List.append_assoc]
  rw [show 15 * j + 5 = [0, n, 1].length + (15 * j + 2) by simp; ring, getD_append_length,
    getD_append_lt (by rw [length_flatten_ofFn _ 15 (fun _ => rfl)]; omega)]
  exact getD_flatten_ofFn (fun j : Fin n => recW (p j)) 15 (fun _ => rfl) ⟨j, hj⟩ 2 (by omega)

theorem getD_w {j : ℕ} (hj : j < n) :
    (stdInst n p w ++ int D).getD (15 * n + 11 + 3 * j) 0 = w j := by
  have hn : n ≠ 0 := by omega
  unfold stdInst
  rw [if_neg hn]
  simp only [List.append_assoc]
  have hR := length_flatten_ofFn (fun j : Fin n => recW (p j)) 15 (fun _ => rfl)
  rw [show 15 * n + 11 + 3 * j = [0, n, 1].length + ((List.ofFn fun j : Fin n => recW (p j)).flatten.length
      + ([0].length + ([1, 4, 1, 0, 0, 0].length + (3 * j + 1)))) by simp [hR]; ring,
    getD_append_length, getD_append_length, getD_append_length, getD_append_length,
    getD_append_lt (by rw [length_flatten_ofFn _ 3 (fun _ => rfl)]; omega)]
  exact getD_flatten_ofFn (fun j : Fin n => [0, w j, 0]) 3 (fun _ => rfl) ⟨j, hj⟩ 1 (by omega)

theorem getD_sign : (stdInst n p w ++ int D).getD ((stdInst n p w ++ int D).length - 2) 0 =
    if D < 0 then 1 else 0 := by
  rw [List.length_append, show (int D).length = 2 from rfl, Nat.add_sub_cancel,
    show (stdInst n p w).length = (stdInst n p w).length + 0 by rfl, getD_append_length]
  rfl

theorem getD_abs : (stdInst n p w ++ int D).getD ((stdInst n p w ++ int D).length - 1) 0 =
    D.natAbs := by
  rw [List.length_append, show (int D).length = 2 from rfl,
    show (stdInst n p w).length + 2 - 1 = (stdInst n p w).length + 1 by omega, getD_append_length]
  rfl

theorem shape_std : Shape (stdInst n p w ++ int D) := by
  have hl := length_stdInst n p w
  rw [Shape, nU_std, List.length_append, hl, show (int D).length = 2 from rfl]
  refine ⟨by split_ifs <;> omega, fun j hj => ?_⟩
  rw [if_neg (by omega)]
  omega

theorem pU_std {j : ℕ} (hj : j < n) : pU (stdInst n p w ++ int D) j = p j := by
  unfold pU; rw [nU_std, if_pos hj, getD_p n p w D hj]

theorem wU_std {j : ℕ} (hj : j < n) : wU (stdInst n p w ++ int D) j = w j := by
  unfold wU; rw [nU_std, if_pos hj, getD_w n p w D hj]

theorem ansU_std : ansU (stdInst n p w ++ int D) =
    [if 0 ≤ D ∧ (opt p w n : ℤ) ≤ D then 1 else 0] := by
  unfold ansU
  rw [getD_sign, getD_abs, nU_std,
    opt_congr (fun j hj => pU_std n p w D hj) (fun j hj => wU_std n p w D hj)]
  congr 1
  by_cases hD : D < 0
  · rw [if_neg (by simp [hD]), if_neg (by omega)]
  · rw [if_neg hD]
    have : ((D.natAbs : ℕ) : ℤ) = D := Int.natAbs_of_nonneg (by omega)
    by_cases h : opt p w n ≤ D.natAbs
    · rw [if_pos ⟨rfl, h⟩, if_pos ⟨by omega, by omega⟩]
    · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => by omega)]

end WordReading

/-! ### Smith's rule decides `1||ΣwjCj` -/

section Glue
open Lax434175.Sanity Lax434175.StandardReading Lax434175.Results
open Lax808846Proofs.Compile Lax808846Proofs.Transfer Lax434175Proofs.Cost

/-- The memory layout of the program. -/
def smithLayout : Layout :=
  ⟨["L", "i", "v", "n", "q", "j", "tm", "tot", "s", "d", "x", "y", "c", "wd", "md", "hi", "i1",
    "i2", "k"], ["a", "P", "W", "A", "T"], 8⟩

theorem smithCom_ok : Com.Ok smithLayout smithCom := by
  simp [smithCom, msort, mpass, mblock, mstep, copyAT, minAssign, cmpSmith, fillBody, sumBody,
    Lax434175Proofs.IsemPrograms.prelude, Lax434175Proofs.Cost.forLoop,
    Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, incr, V, smithLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem ansU_eq {u : List ℕ} {x : Inst OperationsFamily.family singleWC} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at singleWC) u x D) :
    ansU u = verdict (P := problem OperationsFamily.family singleWC) x D := by
  rw [word_eq x h, ansU_std]
  unfold verdict
  have hd := decides_iff x (D : ℚ)
  by_cases hD : 0 ≤ D ∧ (opt (pOf x) (wOf x) x.base.jobs : ℤ) ≤ D
  · rw [if_pos hD, if_pos (hd.mpr (by exact_mod_cast hD.2))]
  · rw [if_neg hD, if_neg (fun h' => hD ?_)]
    have h2 : (opt (pOf x) (wOf x) x.base.jobs : ℚ) ≤ (D : ℚ) := hd.mp h'
    have h3 : (opt (pOf x) (wOf x) x.base.jobs : ℤ) ≤ D := by exact_mod_cast h2
    exact ⟨by omega, h3⟩

theorem solves_smith : Solves smithLayout smithCom (Tapes (StandardReading.ops.at singleWC))
    (fun v => ansU v.tail) (fun v => bndS v.tail) (fun v => costS v.tail) where
  ok := smithCom_ok
  inp := by
    rintro v ⟨u, x, D, hx, rfl⟩ e he
    simp only [List.tail_cons, bndS]
    have hK : u.length + Lax434175.Results.maxEntry u + 2 <
        64 * (u.length + Lax434175.Results.maxEntry u + 2) ^ 4 := by
      have hK2 : 2 ≤ u.length + Lax434175.Results.maxEntry u + 2 := by omega
      generalize u.length + Lax434175.Results.maxEntry u + 2 = K at hK2 ⊢
      have : K * 1 ≤ K * K ^ 3 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
      nlinarith
    rcases List.mem_cons.mp he with rfl | he
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max he
      change e ≤ Lax434175.Results.maxEntry u at this
      omega
  run := by
    rintro v ⟨u, x, D, hx, rfl⟩
    obtain ⟨σ', hr, ho⟩ := run_smith u (by rw [word_eq x hx]; exact shape_std _ _ _ _)
    exact ⟨_, σ', hr, ho⟩

/-- The cost of the program against `(n + 1) (log₂ n + 1)`. -/
theorem cost_le {u : List ℕ} {x : Inst OperationsFamily.family singleWC} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at singleWC) u x D) :
    costS u ≤ 400 * ((x.base.jobs + 1) * (Nat.log 2 x.base.jobs + 1)) := by
  have hu := word_eq x h
  have hl : u.length ≤ 18 * x.base.jobs + 12 := by
    rw [hu, List.length_append, length_stdInst, show (int D).length = 2 from rfl]
    split_ifs <;> omega
  have hn : nU u = x.base.jobs := by rw [hu, nU_std]
  unfold costS sortCost
  rw [hn]
  set n := x.base.jobs
  set l := Nat.log 2 n
  have h1 : 13 * u.length + 50 * n + 50 ≤ (284 * n + 212) * (l + 1) := by
    have : 284 * n + 212 ≤ (284 * n + 212) * (l + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  nlinarith

/--
---
conclusion: Lax434175.Sanity.smith
---
Smith's rule as a word RAM program in IMP+: it reads the standard word into memory, copies the
processing times and weights into two arrays, sorts the jobs by bottom-up merge sort with the
comparison `p_i w_j ≤ p_j w_i` (jobs of weight `0` last) in `⌈log₂ n⌉` passes of linear cost,
adds up the weighted completion times of the sorted order and compares with the threshold. Run
in this order without idle time, the jobs pay `Σ w_j p_j` plus, for every pair, the smaller of
`p_i w_j` and `p_j w_i`, and every schedule on one machine pays at least that (the jobs before
each job in the order of completion fill the machine up to its completion).
-/
theorem smith :
    DecidesWithin (StandardReading.ops.at singleWC) fun x =>
      (ResultParameters.Ops.n singleWC x + 1) * (Nat.log 2 (ResultParameters.Ops.n singleWC x) + 1) +
        inputSize (StandardReading.ops.at singleWC) x := by
  refine decidesWithin_of_solves _ solves_smith
    (fun u x D h => by simp only [List.tail_cons]; exact ansU_eq h) 4000 (fun u x D h => ?_)
    (fun u x D h ℓ hℓ => ?_)
  · simp only [List.tail_cons]
    have := cost_le h
    change 10 * costS u + 1 ≤ 4000 * ((x.base.jobs + 1) * (Nat.log 2 x.base.jobs + 1) + _ + 1)
    nlinarith
  · simp only [List.tail_cons]
    have hℓ' : (u.length + Lax434175.Results.maxEntry u + 2) ^ 4000 ≤ 2 ^ ℓ := hℓ
    have hK2 : 2 ≤ u.length + Lax434175.Results.maxEntry u + 2 := by omega
    have hB : bndS u = 64 * (u.length + Lax434175.Results.maxEntry u + 2) ^ 4 := rfl
    rw [hB]
    generalize u.length + Lax434175.Results.maxEntry u + 2 = K at hℓ' hK2 ⊢
    have hpow : K ^ 13 ≤ 2 ^ ℓ := le_trans (Nat.pow_le_pow_right (by omega) (by norm_num)) hℓ'
    have h9 : 512 ≤ K ^ 9 := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ K ^ 9 := Nat.pow_le_pow_left hK2 9
    have h4 : 16 ≤ K ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ K ^ 4 := Nat.pow_le_pow_left hK2 4
    have e13 : K ^ 13 = K ^ 9 * K ^ 4 := by ring
    refine ⟨by omega, ?_⟩
    simp only [Layout.span, smithLayout, List.length_cons, List.length_nil]
    apply max_le
    · nlinarith
    · nlinarith

end Glue

end Lax434175Proofs.Smith
