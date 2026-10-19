import Mathlib.Tactic
import Lax434175.ThresholdWords
import Lax434175Proofs.PadProgram
import Lax808846Proofs.Spec
import Lax434175Proofs.ResultTransfer
import Lax496464.WH_A5_Bridges
import Lax434175Proofs.ThresholdWords

/-!
The word map of a step between objectives (`ThresholdWords.stepWord`) as a word
RAM program written in IMP+.

The program reads the word into an array. A word too short for its second
number is copied. Otherwise the program copies the prefix, rewrites the rows of
release date, weight and due date, accumulating what the new threshold needs, and
writes the new threshold. The arithmetic is on natural numbers: the threshold is
its sign `ng` and absolute value `ab`, `g` is `1` exactly when it is negative,
and every case distinction is a product with `1 - (1 - x)`, which is `0` or `1`.
-/

namespace Lax434175Proofs.ThresholdProgram

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer
open Lax434175.ThresholdWords

-- The arithmetic on numbers

/-- `1` for a positive number, `0` for zero. -/
def indN (x : ℕ) : ℕ := 1 - (1 - x)

theorem indN_zero : indN 0 = 0 := rfl

theorem indN_pos {x : ℕ} (h : 0 < x) : indN x = 1 := by unfold indN; omega

theorem indN_le (x : ℕ) : indN x ≤ 1 := by unfold indN; omega

/-- `1` exactly when the threshold of sign `ng` and absolute value `ab` is negative. -/
def gN (ng ab : ℕ) : ℕ := indN ng * indN ab

/-- The new due date. -/
def dueN : StepMode → ℕ → ℕ → ℕ → ℕ → ℕ
  | .lateConst, g, ab, _, _ => (1 - g) * ab
  | .lateShift, g, ab, _, d => (d + (1 - g) * ab) - g * ab
  | .toRelease, _, _, r, _ => r
  | .shift, _, _, _, d => d
  | .weightedShift, _, _, _, d => d

/-- The accumulator after one more row. -/
def accN : StepMode → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | .lateConst, _, _, s, _, _, _ => s
  | .lateShift, ng, ab, s, _, _, d => s + indN ng * indN (ab - d)
  | .toRelease, _, _, s, _, _, _ => s
  | .shift, _, _, s, r, _, _ => s + r
  | .weightedShift, _, _, s, r, w, _ => s + w * r

/-- The sign of the new threshold. -/
def signN : StepMode → ℕ → ℕ → ℕ → ℕ → ℕ
  | .lateConst, g, _, _, _ => g
  | .lateShift, g, n, s, _ => indN (s + g * (1 - n))
  | .toRelease, g, _, _, _ => g
  | .shift, g, _, s, ab => indN (g + (s - ab))
  | .weightedShift, g, _, s, ab => indN (g + (s - ab))

/-- The absolute value of the new threshold. -/
def absN : StepMode → ℕ → ℕ → ℕ → ℕ → ℕ
  | .lateConst, g, _, _, _ => g
  | .lateShift, g, n, s, _ => indN (s + g * (1 - n))
  | .toRelease, _, _, _, ab => ab
  | .shift, g, _, s, ab => g * (ab + s) + (1 - g) * ((ab - s) + (s - ab))
  | .weightedShift, g, _, s, ab => g * (ab + s) + (1 - g) * ((ab - s) + (s - ab))

/-- The accumulator after the first `j` rows. -/
def sAt (mode : StepMode) (ng ab : ℕ) (r w d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => accN mode ng ab (sAt mode ng ab r w d j) (r j) (w j) (d j)

theorem readThr_neg (ng ab : ℕ) : readThr ng ab < 0 ↔ gN ng ab = 1 := by
  unfold readThr gN
  rcases Nat.eq_zero_or_pos ng with h | h <;> rcases Nat.eq_zero_or_pos ab with h' | h'
  all_goals (simp only [indN_zero, indN_pos, *]; simp) <;> omega

theorem gN_cases (ng ab : ℕ) :
    (gN ng ab = 1 ∧ readThr ng ab = -(ab : ℤ) ∧ 0 < ab) ∨ (gN ng ab = 0 ∧ readThr ng ab = ab) := by
  unfold readThr gN
  rcases Nat.eq_zero_or_pos ng with h | h <;> rcases Nat.eq_zero_or_pos ab with h' | h'
  · subst h; subst h'; right; simp [indN_zero]
  · subst h; right; simp [indN_zero]
  · subst h'; right; simp [indN_zero]
  · left; simp [indN_pos h, indN_pos h']; omega

theorem due_eq (mode : StepMode) (ng ab r d : ℕ) :
    dueN mode (gN ng ab) ab r d = newDue mode (readThr ng ab) r d := by
  rcases gN_cases ng ab with ⟨hg, hD, _⟩ | ⟨hg, hD⟩ <;> rw [hg, hD] <;>
    cases mode <;> simp only [dueN, newDue] <;> omega

theorem sAt_lateShift (ng ab : ℕ) (r w d : ℕ → ℕ) (j : ℕ) :
    0 < sAt .lateShift ng ab r w d j ↔ ∃ t < j, (d t : ℤ) + readThr ng ab < 0 := by
  induction j with
  | zero => simp [sAt]
  | succ j ih =>
    simp only [sAt, accN]
    have hP : (d j : ℤ) + readThr ng ab < 0 ↔ 0 < indN ng * indN (ab - d j) := by
      unfold readThr
      rcases Nat.eq_zero_or_pos ng with h | h
      · subst h; simp [indN_zero]; omega
      · rcases Nat.eq_zero_or_pos (ab - d j) with h' | h'
        · rw [h', indN_zero, indN_pos h]; simp; omega
        · rw [indN_pos h, indN_pos h']; simp; omega
    constructor
    · intro hs
      by_cases h0 : 0 < sAt .lateShift ng ab r w d j
      · obtain ⟨t, ht, h⟩ := ih.mp h0; exact ⟨t, by omega, h⟩
      · exact ⟨j, by omega, hP.mpr (by omega)⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · have := ih.mpr ⟨t, ht, h⟩; omega
      · have := hP.mp h; omega

theorem sAt_shift (ng ab : ℕ) (r w d : ℕ → ℕ) (j : ℕ) :
    (sAt .shift ng ab r w d j : ℤ) = ∑ t ∈ Finset.range j, (r t : ℤ) := by
  induction j with
  | zero => simp [sAt]
  | succ j ih => rw [Finset.sum_range_succ, ← ih]; simp [sAt, accN]

theorem sAt_weighted (ng ab : ℕ) (r w d : ℕ → ℕ) (j : ℕ) :
    (sAt .weightedShift ng ab r w d j : ℤ) = ∑ t ∈ Finset.range j, (w t : ℤ) * (r t : ℤ) := by
  induction j with
  | zero => simp [sAt]
  | succ j ih => rw [Finset.sum_range_succ, ← ih]; simp [sAt, accN]

theorem thr_shift (g ab s : ℕ) (D : ℤ)
    (h : (g = 1 ∧ D = -(ab : ℤ) ∧ 0 < ab) ∨ (g = 0 ∧ D = ab)) :
    [indN (g + (s - ab)), g * (ab + s) + (1 - g) * ((ab - s) + (s - ab))] = thrWord (D - s) := by
  unfold thrWord
  rcases h with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩
  · rw [indN_pos (by omega)]; simp; omega
  · rcases Nat.eq_zero_or_pos (s - ab) with h' | h'
    · rw [h', indN_zero]; simp; omega
    · rw [Nat.zero_add, indN_pos h']; simp; omega

theorem thr_eq (mode : StepMode) (n ng ab : ℕ) (r w d : ℕ → ℕ) :
    [signN mode (gN ng ab) n (sAt mode ng ab r w d n) ab,
      absN mode (gN ng ab) n (sAt mode ng ab r w d n) ab] =
      thrWord (newThr mode n (readThr ng ab) r w d) := by
  have hc := gN_cases ng ab
  cases mode with
  | lateConst =>
    simp only [signN, absN, newThr, thrWord]
    rcases hc with ⟨hg, hD, _⟩ | ⟨hg, hD⟩ <;> rw [hg, hD] <;>
      simp only [List.cons.injEq, and_true] <;> refine ⟨?_, ?_⟩ <;> (repeat' split) <;> omega
  | toRelease =>
    show [gN ng ab, ab] = thrWord (readThr ng ab)
    rcases hc with ⟨hg, hD, hab⟩ | ⟨hg, hD⟩
    · rw [hg, hD]; simp [thrWord, hab]
    · rw [hg, hD]; simp [thrWord]
  | lateShift =>
    simp only [signN, absN, newThr, thrWord]
    have hs := sAt_lateShift ng ab r w d n
    generalize sAt .lateShift ng ab r w d n = s at hs
    have key : 0 < s + gN ng ab * (1 - n) ↔
        (n = 0 ∧ readThr ng ab < 0) ∨ ∃ j < n, (d j : ℤ) + readThr ng ab < 0 := by
      rw [← hs, readThr_neg]
      rcases hc with ⟨hg, -, -⟩ | ⟨hg, -⟩ <;> rw [hg] <;>
        rcases Nat.eq_zero_or_pos n with hn | hn <;> simp [hn]; omega
    by_cases hk : 0 < s + gN ng ab * (1 - n)
    · rw [indN_pos hk]; simp only [if_pos (key.mp hk)]; rfl
    · rw [show s + gN ng ab * (1 - n) = 0 by omega, indN_zero]
      simp only [if_neg (fun h => hk (key.mpr h))]; rfl
  | shift =>
    simp only [signN, absN, newThr]
    rw [← sAt_shift ng ab r w d n]
    exact thr_shift _ _ _ _ hc
  | weightedShift =>
    simp only [signN, absN, newThr]
    rw [← sAt_weighted ng ab r w d n]
    exact thr_shift _ _ _ _ hc

/-- The accumulator stays below `j (K² + 1)` when the numbers are at most `K`. -/
theorem sAt_le (mode : StepMode) (ng ab : ℕ) (r w d : ℕ → ℕ) (K : ℕ) :
    ∀ j, (∀ t < j, r t ≤ K ∧ w t ≤ K) → sAt mode ng ab r w d j ≤ j * (K * K + 1)
  | 0, _ => by simp [sAt]
  | j + 1, h => by
    have ih := sAt_le mode ng ab r w d K j fun t ht => h t (by omega)
    obtain ⟨hr, hw⟩ := h j (by omega)
    have hKK : K ≤ K * K + 1 := by nlinarith
    have hwr : w j * r j ≤ K * K := Nat.mul_le_mul hw hr
    have hi : indN ng * indN (ab - d j) ≤ 1 :=
      (Nat.mul_le_mul (indN_le ng) (indN_le _)).trans (by norm_num)
    have e : (j + 1) * (K * K + 1) = j * (K * K + 1) + (K * K + 1) := by ring
    rw [e]
    cases mode <;> simp only [sAt, accN] <;> omega

-- Lists

theorem map_range_getD (u : List ℕ) {m : ℕ} (h : m ≤ u.length) :
    (List.range m).map (fun j => u.getD j 0) = u.take m := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1; omega)]
  rfl

theorem ofFn_flatten (n : ℕ) (f : ℕ → List ℕ) :
    (List.ofFn fun j : Fin n => f j).flatten = (List.range n).flatMap f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.range_succ,
      List.flatMap_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.flatMap_cons, List.flatMap_nil]
    rw [ih]

-- The program

abbrev V (x : String) : Expr := .var x
abbrev A (e : Expr) : Expr := .get "a" e
/-- `1 - (1 - e)`. -/
abbrev ind (e : Expr) : Expr := .sub (.lit 1) (.sub (.lit 1) e)

/-- `x := x + 1` -/
abbrev incr (x : String) : Com := .assign x (.add (.var x) (.lit 1))

/-- Write `a[0], …, a[lim - 1]`. -/
def copyTo (lim : String) : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var lim)) (.seq (.write (A (V "i"))) (incr "i")))

def dueE : StepMode → Expr
  | .lateConst => .mul (.sub (.lit 1) (V "g")) (V "ab")
  | .lateShift => .sub (.add (A (.add (V "k") (.lit 2))) (.mul (.sub (.lit 1) (V "g")) (V "ab")))
      (.mul (V "g") (V "ab"))
  | .toRelease => A (V "k")
  | .shift => A (.add (V "k") (.lit 2))
  | .weightedShift => A (.add (V "k") (.lit 2))

def accE : StepMode → Expr
  | .lateConst => V "s"
  | .lateShift => .add (V "s") (.mul (ind (V "ng")) (ind (.sub (V "ab") (A (.add (V "k") (.lit 2))))))
  | .toRelease => V "s"
  | .shift => .add (V "s") (A (V "k"))
  | .weightedShift => .add (V "s") (.mul (A (.add (V "k") (.lit 1))) (A (V "k")))

def signE : StepMode → Expr
  | .lateConst => V "g"
  | .lateShift => ind (.add (V "s") (.mul (V "g") (.sub (.lit 1) (V "n"))))
  | .toRelease => V "g"
  | .shift => ind (.add (V "g") (.sub (V "s") (V "ab")))
  | .weightedShift => ind (.add (V "g") (.sub (V "s") (V "ab")))

/-- `g (ab + s) + (1 - g) ((ab - s) + (s - ab))` -/
def shiftAbs : Expr :=
  .add (.mul (V "g") (.add (V "ab") (V "s")))
    (.mul (.sub (.lit 1) (V "g")) (.add (.sub (V "ab") (V "s")) (.sub (V "s") (V "ab"))))

def absE : StepMode → Expr
  | .lateConst => V "g"
  | .lateShift => ind (.add (V "s") (.mul (V "g") (.sub (.lit 1) (V "n"))))
  | .toRelease => V "ab"
  | .shift => shiftAbs
  | .weightedShift => shiftAbs

/-- One row: release date, weight, new due date; accumulate; move on. -/
def row (mode : StepMode) : Com :=
  .seq (.write (A (V "k"))) <| .seq (.write (A (.add (V "k") (.lit 1)))) <|
  .seq (.write (dueE mode)) <| .seq (.assign "s" (accE mode)) <|
  .seq (.assign "k" (.add (V "k") (.lit 3))) (incr "j")

/-- `3 n + 2` -/
abbrev three : Expr := .add (.mul (.lit 3) (V "n")) (.lit 2)

/-- The rewriting of a word long enough. -/
def long (mode : StepMode) : Com :=
  .seq (.assign "bs" (.sub (V "L") three)) <|
  .seq (.assign "ng" (A (.sub (V "L") (.lit 2)))) <|
  .seq (.assign "ab" (A (.sub (V "L") (.lit 1)))) <|
  .seq (.assign "g" (.mul (ind (V "ng")) (ind (V "ab")))) <|
  .seq (copyTo "bs") <|
  .seq (.assign "k" (V "bs")) <| .seq (.assign "s" (.lit 0)) <|
  .seq (.seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "n")) (row mode))) <|
  .seq (.write (signE mode)) (.write (absE mode))

/-- The whole program. -/
def com (mode : StepMode) : Com :=
  .seq (.read "L") <| .seq (Lax434175Proofs.PadProgram.readLoop "a" "L") <|
  .seq (.assign "n" (A (.lit 1))) <|
  .ite (.lt (V "L") three) (copyTo "L") (long mode)

def layout : Layout := ⟨["L", "i", "v", "n", "bs", "ng", "ab", "g", "k", "s", "j"], ["a"], 10⟩

theorem com_ok (mode : StepMode) : Com.Ok layout (com mode) := by
  cases mode <;>
  simp [com, long, row, copyTo, dueE, accE, signE, absE, shiftAbs,
    Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

-- Evaluation

section Eval
variable {B : ℕ} {σ : Env}

theorem ev_lit {n : ℕ} (h : n < B) : (Expr.lit n).evalB B σ = some n := evalB_lit h

theorem ev_var {x : String} {v : ℕ} (h : σ.vars x = v) (hv : v < B) :
    (Expr.var x).evalB B σ = some v := by subst h; exact evalB_var hv

theorem ev_add {e f : Expr} {m n : ℕ} (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n)
    (h : m + n < B) : (Expr.add e f).evalB B σ = some (m + n) := evalB_bin he hf h

theorem ev_mul {e f : Expr} {m n : ℕ} (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n)
    (h : m * n < B) : (Expr.mul e f).evalB B σ = some (m * n) := evalB_bin he hf h

theorem ev_sub {e f : Expr} {m n : ℕ} (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) :
    (Expr.sub e f).evalB B σ = some (m - n) :=
  evalB_bin he hf (lt_of_le_of_lt (Nat.sub_le _ _) (Expr.eval_and_lt_of_evalB he).2)

theorem ev_ind {e : Expr} {m : ℕ} (he : e.evalB B σ = some m) (h1 : 1 < B) :
    (ind e).evalB B σ = some (indN m) := ev_sub (ev_lit h1) (ev_sub (ev_lit h1) he)

theorem ev_A {e : Expr} {k N : ℕ} {f : ℕ → ℕ} (he : e.evalB B σ = some k)
    (ha : σ.arrs "a" = arrOf N f) (hk : k < N) (hv : f k < B) :
    (A e).evalB B σ = some (f k) :=
  evalB_get he (by rw [ha]; exact getElem?_arrOf f hk) hv

end Eval

-- Copying

theorem copy_run {B N m : ℕ} {f : ℕ → ℕ} (lim : String) (hlim : lim ≠ "i") (hNB : N < B)
    (hm : m ≤ N) (hf : ∀ j < N, f j < B) (σ : Env) (ha : σ.arrs "a" = arrOf N f)
    (hl : σ.vars lim = m) :
    ∃ σ', Run B (copyTo lim) σ σ' (11 * m + 6) ∧ σ'.out = σ.out ++ (List.range m).map f ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) := by
  let I : Env → Prop := fun τ => τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
    (∀ y, y ≠ "i" → τ.vars y = σ.vars y) ∧
    τ.out = σ.out ++ (List.range (τ.vars "i")).map f ∧ τ.vars "i" ≤ m
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < m) (.seq (.write (A (V "i"))) (incr "i"))
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 7 := by
    rintro τ ⟨⟨harr, hinp, hv, hout, hle⟩, hlt⟩
    have hget : (A (V "i")).evalB B τ = some (f (τ.vars "i")) :=
      ev_A (ev_var rfl (by omega)) ((congrFun harr "a").trans ha) (by omega) (hf _ (by omega))
    refine ⟨_, (Run.seq (Run.write hget)
      (Run.assign (x := "i") (ev_add (σ := { τ with out := τ.out ++ [f (τ.vars "i")] })
        (ev_var rfl (by show τ.vars "i" < B; omega)) (ev_lit (n := 1) (by omega))
        (by show τ.vars "i" + 1 < B; omega)))).mono (by simp), ?_, ?_⟩
    · refine ⟨by simp [harr], by simp [hinp], fun y hy => by simp [hy, hv y hy], ?_, by simp; omega⟩
      simp [hout, List.range_succ]
    · simp
  obtain ⟨σ', hrun, ⟨harr, hinp, hv, hout, -⟩, hi⟩ :=
    (Spec.forRangeZero "i" lim I m 7 (by omega) (fun τ h => h.2.2.2.2)
      (fun τ h => by rw [h.2.2.1 lim hlim, hl]) hbody).run
      (σ := σ) ⟨by simp, by simp, fun y hy => by simp [hy], by simp, by simp⟩
  refine ⟨σ', hrun.mono (by omega), by rw [hout, hi], harr, hinp, hv⟩

-- Evaluating the expressions of a row and of the threshold

section Exprs
variable {B N K : ℕ} {f : ℕ → ℕ} {σ : Env}

theorem le_of_one {g x : ℕ} (hg : g ≤ 1) : g * x ≤ x ∧ (1 - g) * x ≤ x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with rfl | rfl <;> simp

theorem ev_due (mode : StepMode) {g ab kk : ℕ} (ha : σ.arrs "a" = arrOf N f)
    (hfK : ∀ j < N, f j ≤ K) (hk : σ.vars "k" = kk) (hkN : kk + 2 < N) (hg : σ.vars "g" = g)
    (hg1 : g ≤ 1) (hab : σ.vars "ab" = ab) (habK : ab ≤ K) (hNK : N ≤ K + 2) (hB : 4 * K + 8 < B) :
    (dueE mode).evalB B σ = some (dueN mode g ab (f kk) (f (kk + 2))) := by
  obtain ⟨h1, h2⟩ := le_of_one (x := ab) hg1
  have hd := hfK (kk + 2) hkN
  have hr := hfK kk (by omega)
  cases mode with
  | lateConst =>
    simp only [dueN]
    exact ev_mul (ev_sub (ev_lit (by omega)) (ev_var hg (by omega))) (ev_var hab (by omega))
      (by omega)
  | lateShift =>
    simp only [dueN]
    exact ev_sub (ev_add (ev_A (k := kk + 2) (ev_add (ev_var hk (by omega)) (ev_lit (by omega)) (by omega)) ha hkN
      (by omega)) (ev_mul (ev_sub (ev_lit (by omega)) (ev_var hg (by omega)))
        (ev_var hab (by omega)) (by omega)) (by omega))
      (ev_mul (ev_var hg (by omega)) (ev_var hab (by omega)) (by omega))
  | toRelease => simp only [dueN]; exact ev_A (k := kk) (ev_var hk (by omega)) ha (by omega) (by omega)
  | shift =>
    simp only [dueN]
    exact ev_A (k := kk + 2) (ev_add (ev_var hk (by omega)) (ev_lit (by omega)) (by omega)) ha hkN (by omega)
  | weightedShift =>
    simp only [dueN]
    exact ev_A (k := kk + 2) (ev_add (ev_var hk (by omega)) (ev_lit (by omega)) (by omega)) ha hkN (by omega)

theorem ev_acc (mode : StepMode) {ng ab s kk : ℕ} (ha : σ.arrs "a" = arrOf N f)
    (hfK : ∀ j < N, f j ≤ K) (hk : σ.vars "k" = kk) (hkN : kk + 2 < N) (hs : σ.vars "s" = s)
    (hsK : s ≤ K * K * K + K) (hng : σ.vars "ng" = ng) (hngK : ng ≤ K) (hab : σ.vars "ab" = ab)
    (habK : ab ≤ K) (hNK : N ≤ K + 2)
    (hB : 2 * (K * K * K) + 12 * (K * K) + 24 * K + 16 ≤ B) :
    (accE mode).evalB B σ = some (accN mode ng ab s (f kk) (f (kk + 1)) (f (kk + 2))) := by
  have hd := hfK (kk + 2) hkN
  have hw := hfK (kk + 1) (by omega)
  have hr := hfK kk (by omega)
  have hwr : f (kk + 1) * f kk ≤ K * K := Nat.mul_le_mul hw hr
  have hi : ∀ a b, indN a * indN b ≤ 1 := fun a b =>
    (Nat.mul_le_mul (indN_le a) (indN_le b)).trans (by norm_num)
  generalize K * K * K = P3 at hsK hB
  generalize K * K = P2 at hwr hB
  cases mode with
  | lateConst => simp only [accN]; exact ev_var hs (by omega)
  | lateShift =>
    simp only [accN]
    exact ev_add (ev_var hs (by omega)) (ev_mul (ev_ind (ev_var hng (by omega)) (by omega))
      (ev_ind (ev_sub (ev_var hab (by omega)) (ev_A (k := kk + 2) (ev_add (ev_var hk (by omega))
        (ev_lit (by omega)) (by omega)) ha hkN (by omega))) (by omega)) (by have := hi ng (ab - f (kk + 2)); omega))
      (by have := hi ng (ab - f (kk + 2)); omega)
  | toRelease => simp only [accN]; exact ev_var hs (by omega)
  | shift =>
    simp only [accN]
    exact ev_add (ev_var hs (by omega)) (ev_A (k := kk) (ev_var hk (by omega)) ha (by omega)
      (by omega)) (by omega)
  | weightedShift =>
    simp only [accN]
    exact ev_add (ev_var hs (by omega)) (ev_mul (ev_A (k := kk + 1) (ev_add (ev_var hk (by omega))
      (ev_lit (by omega)) (by omega)) ha (by omega) (by omega))
      (ev_A (k := kk) (ev_var hk (by omega)) ha (by omega) (by omega)) (by omega)) (by omega)

theorem ev_sign (mode : StepMode) {g ab s n : ℕ} (hs : σ.vars "s" = s)
    (hsK : s ≤ K * K * K + K) (hg : σ.vars "g" = g) (hg1 : g ≤ 1) (hab : σ.vars "ab" = ab)
    (habK : ab ≤ K) (hn : σ.vars "n" = n) (hnK : n ≤ K)
    (hB : 2 * (K * K * K) + 12 * (K * K) + 24 * K + 16 ≤ B) :
    (signE mode).evalB B σ = some (signN mode g n s ab) := by
  obtain ⟨h1, h2⟩ := le_of_one (x := 1 - n) hg1
  generalize K * K * K = P3 at hsK hB
  cases mode with
  | lateConst => simp only [signN]; exact ev_var hg (by omega)
  | lateShift =>
    simp only [signN]
    exact ev_ind (ev_add (ev_var hs (by omega)) (ev_mul (ev_var hg (by omega))
      (ev_sub (ev_lit (by omega)) (ev_var hn (by omega))) (by omega)) (by omega)) (by omega)
  | toRelease => simp only [signN]; exact ev_var hg (by omega)
  | shift =>
    simp only [signN]
    exact ev_ind (ev_add (ev_var hg (by omega)) (ev_sub (ev_var hs (by omega))
      (ev_var hab (by omega))) (by omega)) (by omega)
  | weightedShift =>
    simp only [signN]
    exact ev_ind (ev_add (ev_var hg (by omega)) (ev_sub (ev_var hs (by omega))
      (ev_var hab (by omega))) (by omega)) (by omega)

theorem ev_shiftAbs {g ab s : ℕ} (hs : σ.vars "s" = s) (hsK : s ≤ K * K * K + K)
    (hg : σ.vars "g" = g) (hg1 : g ≤ 1) (hab : σ.vars "ab" = ab) (habK : ab ≤ K)
    (hB : 2 * (K * K * K) + 12 * (K * K) + 24 * K + 16 ≤ B) :
    shiftAbs.evalB B σ = some (g * (ab + s) + (1 - g) * ((ab - s) + (s - ab))) := by
  obtain ⟨h1, h2⟩ := le_of_one (x := ab + s) hg1
  obtain ⟨h3, h4⟩ := le_of_one (x := (ab - s) + (s - ab)) hg1
  have h5 : g * (ab + s) + (1 - g) * ((ab - s) + (s - ab)) ≤ ab + s := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg1 with rfl | rfl <;> simp; omega
  generalize K * K * K = P3 at hsK hB
  exact ev_add (ev_mul (ev_var hg (by omega)) (ev_add (ev_var hab (by omega)) (ev_var hs (by omega))
    (by omega)) (by omega)) (ev_mul (ev_sub (ev_lit (by omega)) (ev_var hg (by omega)))
      (ev_add (ev_sub (ev_var hab (by omega)) (ev_var hs (by omega)))
        (ev_sub (ev_var hs (by omega)) (ev_var hab (by omega))) (by omega)) (by omega)) (by omega)

theorem ev_abs (mode : StepMode) {g ab s n : ℕ} (hs : σ.vars "s" = s)
    (hsK : s ≤ K * K * K + K) (hg : σ.vars "g" = g) (hg1 : g ≤ 1) (hab : σ.vars "ab" = ab)
    (habK : ab ≤ K) (hn : σ.vars "n" = n) (hnK : n ≤ K)
    (hB : 2 * (K * K * K) + 12 * (K * K) + 24 * K + 16 ≤ B) :
    (absE mode).evalB B σ = some (absN mode g n s ab) := by
  cases mode with
  | lateConst => simp only [absN]; exact ev_var hg (by omega)
  | lateShift => simp only [absN]; exact ev_sign .lateShift hs hsK hg hg1 hab habK hn hnK hB
  | toRelease => simp only [absN]; exact ev_var hab (by omega)
  | shift => simp only [absN]; exact ev_shiftAbs hs hsK hg hg1 hab habK hB
  | weightedShift => simp only [absN]; exact ev_shiftAbs hs hsK hg hg1 hab habK hB

end Exprs

theorem size_dueE (mode : StepMode) : (dueE mode).size ≤ 14 := by cases mode <;> simp [dueE]
theorem size_accE (mode : StepMode) : (accE mode).size ≤ 18 := by cases mode <;> simp [accE]
theorem size_signE (mode : StepMode) : (signE mode).size ≤ 14 := by cases mode <;> simp [signE]
theorem size_absE (mode : StepMode) : (absE mode).size ≤ 24 := by
  cases mode <;> simp [absE, shiftAbs]

-- The rows

/-- The three numbers the program writes for row `t`. -/
def rowOut (mode : StepMode) (f : ℕ → ℕ) (bs g ab t : ℕ) : List ℕ :=
  [f (bs + 3 * t), f (bs + 3 * t + 1), dueN mode g ab (f (bs + 3 * t)) (f (bs + 3 * t + 2))]

theorem row_run (mode : StepMode) {B N K n bs g ng ab : ℕ} {f : ℕ → ℕ} (σ : Env)
    (ha : σ.arrs "a" = arrOf N f) (hfK : ∀ j < N, f j ≤ K) (hN : bs + 3 * n ≤ N)
    (hNK : N ≤ K + 2) (hnK : n ≤ K) (hg1 : g ≤ 1) (habK : ab ≤ K) (hngK : ng ≤ K)
    (hB : 2 * (K * K * K) + 12 * (K * K) + 24 * K + 16 ≤ B)
    (hvn : σ.vars "n" = n) (hvg : σ.vars "g" = g) (hvng : σ.vars "ng" = ng)
    (hvab : σ.vars "ab" = ab) (hk : σ.vars "k" = bs) (hs : σ.vars "s" = 0) :
    ∃ σ', Run B (.seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "n")) (row mode)))
        σ σ' (64 * n + 6) ∧
      σ'.out = σ.out ++ (List.range n).flatMap (rowOut mode f bs g ab) ∧
      σ'.vars "s" = sAt mode ng ab (fun t => f (bs + 3 * t)) (fun t => f (bs + 3 * t + 1))
        (fun t => f (bs + 3 * t + 2)) n ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
      (∀ y, y ≠ "j" → y ≠ "k" → y ≠ "s" → σ'.vars y = σ.vars y) := by
  set S := sAt mode ng ab (fun t => f (bs + 3 * t)) (fun t => f (bs + 3 * t + 1))
    (fun t => f (bs + 3 * t + 2)) with hS
  let I : Env → Prop := fun τ => τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
    (∀ y, y ≠ "j" → y ≠ "k" → y ≠ "s" → τ.vars y = σ.vars y) ∧
    τ.vars "k" = bs + 3 * τ.vars "j" ∧ τ.vars "s" = S (τ.vars "j") ∧
    τ.out = σ.out ++ (List.range (τ.vars "j")).flatMap (rowOut mode f bs g ab) ∧ τ.vars "j" ≤ n
  have hSle : ∀ t ≤ n, S t ≤ K * K * K + K := by
    intro t ht
    have h1 : S t ≤ t * (K * K + 1) := sAt_le mode ng ab (fun t => f (bs + 3 * t))
      (fun t => f (bs + 3 * t + 1)) (fun t => f (bs + 3 * t + 2)) K t
      (fun t' ht' => ⟨hfK _ (by omega), hfK _ (by omega)⟩)
    have h2 : t * (K * K + 1) ≤ K * (K * K + 1) := Nat.mul_le_mul_right _ (by omega)
    have h3 : K * (K * K + 1) = K * K * K + K := by ring
    omega
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "j" < n) (row mode)
      (fun τ τ' => I τ' ∧ τ'.vars "j" = τ.vars "j" + 1) 60 := by
    rintro τ ⟨⟨harr, hinp, hv, hkk, hss, hout, hle⟩, hlt⟩
    set t := τ.vars "j" with ht
    have ha' : τ.arrs "a" = arrOf N f := (congrFun harr "a").trans ha
    have hkN : bs + 3 * t + 2 < N := by omega
    have hvg' : τ.vars "g" = g := (hv "g" (by decide) (by decide) (by decide)).trans hvg
    have hvab' : τ.vars "ab" = ab := (hv "ab" (by decide) (by decide) (by decide)).trans hvab
    have hvng' : τ.vars "ng" = ng := (hv "ng" (by decide) (by decide) (by decide)).trans hvng
    have hP3 : K ≤ K * K * K + K := by omega
    have hsK := hSle t (by omega)
    have hr := hfK (bs + 3 * t) (by omega)
    have hw := hfK (bs + 3 * t + 1) (by omega)
    have e1 : (A (V "k")).evalB B τ = some (f (bs + 3 * t)) :=
      ev_A (ev_var hkk (by omega)) ha' (by omega) (by omega)
    have e2 : (A (.add (V "k") (.lit 1))).evalB B { τ with out := τ.out ++ [f (bs + 3 * t)] } =
        some (f (bs + 3 * t + 1)) :=
      ev_A (ev_add (ev_var hkk (by omega)) (ev_lit (by omega)) (by omega)) ha' (by omega) (by omega)
    have e3 := ev_due mode (B := B) (K := K) (σ := { τ with out := τ.out ++ [f (bs + 3 * t)] ++ [f (bs + 3 * t + 1)] })
      ha' hfK hkk hkN hvg' hg1 hvab' habK hNK (by omega)
    have e4 := ev_acc mode (B := B) (K := K) (σ := { τ with out := τ.out ++ [f (bs + 3 * t)] ++ [f (bs + 3 * t + 1)] ++
        [dueN mode g ab (f (bs + 3 * t)) (f (bs + 3 * t + 2))] })
      ha' hfK hkk hkN hss hsK hvng' hngK hvab' habK hNK hB
    refine ⟨_, (Run.seq (Run.write e1) <| Run.seq (Run.write e2) <| Run.seq (Run.write e3) <|
      Run.seq (Run.assign (x := "s") e4) <|
      Run.seq (Run.assign (x := "k") (ev_add (ev_var (v := bs + 3 * t) (by simpa using hkk)
        (by omega)) (ev_lit (n := 3) (by omega)) (by omega)))
      (Run.assign (x := "j") (ev_add (ev_var (v := t) (by simp [ht]) (by omega))
        (ev_lit (n := 1) (by omega)) (by omega)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have := size_dueE mode; have := size_accE mode
      simp only [size_get, size_var, size_add, size_lit]
      omega
    · simp [harr]
    · simp [hinp]
    · intro y hj hk hs; simp [hj, hk, hs, hv y hj hk hs]
    · simp; omega
    · simp [hS, sAt]
    · simp [hout, List.range_succ, rowOut]
    · simp; omega
    · simp [ht]
  obtain ⟨σ', hrun, ⟨harr, hinp, hv, -, hss, hout, -⟩, hj⟩ :=
    (Spec.forRangeZero "j" "n" I n 60 (by omega) (fun τ h => h.2.2.2.2.2.2)
      (fun τ h => by rw [h.2.2.1 "n" (by decide) (by decide) (by decide), hvn]) hbody).run
      (σ := σ) ⟨by simp, by simp, fun y hy _ _ => by simp [hy], by simp [hk], by simp [hs, hS, sAt],
        by simp, by simp⟩
  exact ⟨σ', hrun.mono (by omega), by rw [hout, hj], by rw [hss, hj], harr, hinp, hv⟩

/-- The rows the word map writes. -/
def rowsNew (mode : StepMode) (u : List ℕ) (b n : ℕ) : List ℕ :=
  (List.range n).flatMap fun t => [u.getD (b + 3 * t) 0, u.getD (b + 3 * t + 1) 0,
    newDue mode (readThr (u.getD (u.length - 2) 0) (u.getD (u.length - 1) 0)) (u.getD (b + 3 * t) 0)
      (u.getD (b + 3 * t + 2) 0)]

theorem stepWord_long (mode : StepMode) (u : List ℕ) (h : ¬ u.length < 3 * u.getD 1 0 + 2) :
    stepWord mode u = u.take (u.length - 2 - 3 * u.getD 1 0) ++
      rowsNew mode u (u.length - 2 - 3 * u.getD 1 0) (u.getD 1 0) ++
      thrWord (newThr mode (u.getD 1 0) (readThr (u.getD (u.length - 2) 0) (u.getD (u.length - 1) 0))
        (fun j => u.getD (u.length - 2 - 3 * u.getD 1 0 + 3 * j) 0)
        (fun j => u.getD (u.length - 2 - 3 * u.getD 1 0 + 3 * j + 1) 0)
        (fun j => u.getD (u.length - 2 - 3 * u.getD 1 0 + 3 * j + 2) 0)) := by
  unfold stepWord
  rw [if_neg h]
  exact congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl (ofFn_flatten (u.getD 1 0) fun t =>
    [u.getD (u.length - 2 - 3 * u.getD 1 0 + 3 * t) 0,
      u.getD (u.length - 2 - 3 * u.getD 1 0 + 3 * t + 1) 0,
      newDue mode (readThr (u.getD (u.length - 2) 0) (u.getD (u.length - 1) 0))
        (u.getD (u.length - 2 - 3 * u.getD 1 0 + 3 * t) 0)
        (u.getD (u.length - 2 - 3 * u.getD 1 0 + 3 * t + 2) 0)])) rfl

-- The whole run

/-- The value bound. -/
def bnd (u : List ℕ) : ℕ := 2 * (u.length + Lax434175.Results.maxEntry u + 2) ^ 3

/-- The cost bound. -/
def cost (u : List ℕ) : ℕ := 200 * (u.length + 1)

open Lax434175.Results in
theorem run_com (mode : StepMode) (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bnd u) (com mode) (initEnv ext (u.length :: u)) σ'
      (cost u) ∧ σ'.out = stepWord mode u := by
  set L := u.length with hL
  set K := u.length + maxEntry u with hK
  set B := bnd u with hBdef
  set f : ℕ → ℕ := fun j => u.getD j 0 with hf
  have hfK : ∀ j, f j ≤ K := fun j =>
    (Lax434175Proofs.PadReduction.getD_le (M := maxEntry u)
      (fun v hv => Lax434175Proofs.PadWord.le_foldr_max hv) j).trans (by omega)
  have hBe : B = 2 * (K * K * K) + 12 * (K * K) + 24 * K + 16 := by
    simp only [hBdef, bnd, hK]; ring
  have hB : 2 * (K * K * K) + 12 * (K * K) + 24 * K + 16 ≤ B := hBe.ge
  have hLK : L ≤ K := by omega
  have hB0 : 24 * K + 16 ≤ B := by omega
  refine ⟨fun _ => L + 2, ?_⟩
  -- reading
  have r0 : Run B (.read "L") (initEnv (fun _ => L + 2) (L :: u))
      { (initEnv (fun _ => L + 2) (L :: u)).setVar "L" L with inp := u } 1 := Run.read rfl
  obtain ⟨σ2, r1, hinp2, hout2, -, hv2, ha2, -⟩ :=
    Lax434175Proofs.PadProgram.read_run (B := B) "a" "L" (by decide) (by decide) u [] (L + 2)
      (by omega) { (initEnv (fun _ => L + 2) (L :: u)).setVar "L" L with inp := u }
      (by simp [initEnv]) (by simp [hL]) (by simp)
      (by simp [initEnv, replicate_eq_arrOf])
      (fun v hv => by have := Lax434175Proofs.PadWord.le_foldr_max hv; unfold maxEntry at hK; omega)
      (by omega)
  have ha : σ2.arrs "a" = arrOf (L + 2) f := ha2
  have hL2 : σ2.vars "L" = L := by rw [hv2 "L" (by decide) (by decide)]; simp
  have hout0 : σ2.out = [] := by rw [hout2]; simp [initEnv]
  set n := f 1 with hn
  have hnK : n ≤ K := hfK 1
  have en : (A (.lit 1)).evalB B σ2 = some n :=
    ev_A (ev_lit (by omega)) ha (by omega) (by omega)
  set s3 : Env := σ2.setVar "n" n with hs3
  have hL3 : s3.vars "L" = L := by simp [hs3, hL2]
  have ec : (Cond.lt (V "L") three).evalB B s3 = some (decide (L < 3 * n + 2)) :=
    evalB_condLt (ev_var hL3 (by omega))
      (ev_add (ev_mul (ev_lit (by omega)) (ev_var (by simp [hs3]) (by omega)) (by omega))
        (ev_lit (by omega)) (by omega))
  by_cases hs : L < 3 * n + 2
  · -- a short word is copied
    obtain ⟨σ4, r4, hout4, -, -, -⟩ := copy_run (B := B) (N := L + 2) (m := L) (f := f) "L"
      (by decide) (by omega) (by omega) (fun j _ => by have := hfK j; omega) s3 (by simpa [hs3] using ha)
      hL3
    refine ⟨σ4, (r0.seq (r1.seq ((Run.assign en).seq
      (Run.ite_true (by rw [ec]; simp [hs]) r4)))).mono ?_, ?_⟩
    · simp only [cost, size_get, size_lit, size_condLt, size_var, size_add, size_mul]
      omega
    · rw [hout4, stepWord, if_pos hs]
      simp only [hs3, out_setVar, hout0, List.nil_append]
      exact (map_range_getD u le_rfl).trans List.take_length
  · -- a long word is rewritten
    set bs := L - (3 * n + 2) with hbs
    set ng := f (L - 2) with hng
    set ab := f (L - 1) with hab
    set g := gN ng ab with hg
    have hngK : ng ≤ K := hfK _
    have habK : ab ≤ K := hfK _
    have hg1 : g ≤ 1 := (Nat.mul_le_mul (indN_le ng) (indN_le ab)).trans (by norm_num)
    have e4 : (Expr.sub (V "L") three).evalB B s3 = some bs :=
      ev_sub (ev_var hL3 (by omega))
        (ev_add (ev_mul (ev_lit (by omega)) (ev_var (by simp [hs3]) (by omega)) (by omega))
          (ev_lit (by omega)) (by omega))
    set s4 : Env := s3.setVar "bs" bs with hs4
    have hL4 : s4.vars "L" = L := by simp [hs4, hL3]
    have e5 : (A (.sub (V "L") (.lit 2))).evalB B s4 = some ng :=
      ev_A (B := B) (k := L - 2) (ev_sub (ev_var hL4 (by omega)) (ev_lit (n := 2) (by omega)))
        (by simpa [hs4, hs3] using ha) (by omega) (by omega)
    set s5 : Env := s4.setVar "ng" ng with hs5
    have e6 : (A (.sub (V "L") (.lit 1))).evalB B s5 = some ab :=
      ev_A (B := B) (k := L - 1) (ev_sub (ev_var (show s5.vars "L" = L by simp [hs5, hL4]) (by omega)) (ev_lit (n := 1) (by omega)))
        (by simpa [hs5, hs4, hs3] using ha) (by omega) (by omega)
    set s6 : Env := s5.setVar "ab" ab with hs6
    have e7 : (Expr.mul (ind (V "ng")) (ind (V "ab"))).evalB B s6 = some g :=
      ev_mul (B := B) (ev_ind (ev_var (by simp [hs6, hs5]) (by omega)) (by omega))
        (ev_ind (ev_var (by simp [hs6]) (by omega)) (by omega)) (lt_of_le_of_lt hg1 (by omega))
    set s7 : Env := s6.setVar "g" g with hs7
    obtain ⟨s8, r8, hout8, harr8, -, hv8⟩ := copy_run (B := B) (N := L + 2) (m := bs) (f := f) "bs"
      (by decide) (by omega) (by omega) (fun j _ => by have := hfK j; omega) s7
      (by simpa [hs7, hs6, hs5, hs4, hs3] using ha) (by simp [hs7, hs6, hs5, hs4])
    have hvar8 : ∀ y, y ≠ "i" → s8.vars y = s7.vars y := hv8
    have e9 : (V "bs").evalB B s8 = some bs :=
      ev_var (by rw [hvar8 "bs" (by decide)]; simp [hs7, hs6, hs5, hs4]) (by omega)
    set s9 : Env := s8.setVar "k" bs with hs9
    set s10 : Env := s9.setVar "s" 0 with hs10
    have ha10 : s10.arrs "a" = arrOf (L + 2) f := by
      simp [hs10, hs9, harr8, hs7, hs6, hs5, hs4, hs3, ha]
    have hv10 : ∀ y, y ≠ "i" → y ≠ "k" → y ≠ "s" → s10.vars y = s7.vars y := fun y h1 h2 h3 => by
      simp [hs10, hs9, h2, h3, hvar8 y h1]
    obtain ⟨s11, r11, hout11, hs11, -, -, hv11⟩ := row_run mode (N := L + 2) (K := K) (n := n)
      (bs := bs) (g := g) (ng := ng) (ab := ab) s10 ha10 (fun j _ => hfK j) (by omega) (by omega)
      hnK hg1 habK hngK hB
      (by rw [hv10 "n" (by decide) (by decide) (by decide)]; simp [hs7, hs6, hs5, hs4, hs3])
      (by rw [hv10 "g" (by decide) (by decide) (by decide)]; simp [hs7])
      (by rw [hv10 "ng" (by decide) (by decide) (by decide)]; simp [hs7, hs6, hs5])
      (by rw [hv10 "ab" (by decide) (by decide) (by decide)]; simp [hs7, hs6])
      (by simp [hs10, hs9]) (by simp [hs10])
    set S := sAt mode ng ab (fun t => f (bs + 3 * t)) (fun t => f (bs + 3 * t + 1))
      (fun t => f (bs + 3 * t + 2)) n with hS
    have hSK : S ≤ K * K * K + K := by
      have h1 : S ≤ n * (K * K + 1) := sAt_le mode ng ab (fun t => f (bs + 3 * t))
        (fun t => f (bs + 3 * t + 1)) (fun t => f (bs + 3 * t + 2)) K n
        (fun t' _ => ⟨hfK _, hfK _⟩)
      have h2 : n * (K * K + 1) ≤ K * (K * K + 1) := Nat.mul_le_mul_right _ hnK
      have h3 : K * (K * K + 1) = K * K * K + K := by ring
      omega
    have hv11' : ∀ y, y ≠ "i" → y ≠ "j" → y ≠ "k" → y ≠ "s" → s11.vars y = s7.vars y :=
      fun y h0 h1 h2 h3 => (hv11 y h1 h2 h3).trans (hv10 y h0 h2 h3)
    have hg11 : s11.vars "g" = g := by
      rw [hv11' "g" (by decide) (by decide) (by decide) (by decide)]; simp [hs7]
    have hab11 : s11.vars "ab" = ab := by
      rw [hv11' "ab" (by decide) (by decide) (by decide) (by decide)]; simp [hs7, hs6]
    have hn11 : s11.vars "n" = n := by
      rw [hv11' "n" (by decide) (by decide) (by decide) (by decide)]
      simp [hs7, hs6, hs5, hs4, hs3]
    have e12 := ev_sign mode (B := B) (K := K) (σ := s11) hs11 hSK hg11 hg1 hab11 habK hn11 hnK hB
    have e13 := ev_abs mode (B := B) (K := K)
      (σ := { s11 with out := s11.out ++ [signN mode g n S ab] }) hs11 hSK hg11 hg1 hab11 habK
      hn11 hnK hB
    have rlong : Run B (long mode) s3 _ _ :=
      (Run.assign e4).seq <| (Run.assign e5).seq <| (Run.assign e6).seq <| (Run.assign e7).seq <|
        r8.seq <| (Run.assign e9).seq <| (Run.assign (x := "s") (ev_lit (n := 0) (by omega))).seq <|
          r11.seq <| (Run.write e12).seq (Run.write e13)
    refine ⟨_, (r0.seq (r1.seq ((Run.assign en).seq
      (Run.ite_false (by rw [ec]; simp [hs]) rlong)))).mono ?_, ?_⟩
    · have := size_signE mode; have := size_absE mode
      simp only [cost, size_get, size_lit, size_condLt, size_var, size_add, size_mul, size_sub]
      omega
    · have hbase : u.length - 2 - 3 * u.getD 1 0 = bs := by
        simp only [hbs, hn, hf]; omega
      have hbsL : bs ≤ u.length := by omega
      have hrows : (List.range n).flatMap (rowOut mode f bs g ab) = rowsNew mode u bs n := by
        refine congrArg (List.flatMap · (List.range n)) (funext fun t => ?_)
        simp only [rowOut, hg, hng, hab, hf, hL, due_eq]
      simp only [hout11, hout8, hs10, hs9, hs7, hs6, hs5, hs4, hs3, out_setVar, hout0]
      rw [stepWord_long mode u hs, hbase, ← hrows, ← map_range_getD u hbsL, ← thr_eq]
      simp only [List.nil_append, List.append_assoc, List.cons_append]
      rfl

-- Polynomial time

/-- The tapes: every word with its length in front. -/
def Tapes : Set (List ℕ) := {y | ∃ u, y = u.length :: u}

theorem solves (mode : StepMode) :
    Solves layout (com mode) Tapes (fun y => stepWord mode y.tail) (fun y => bnd y.tail)
      (fun y => cost y.tail) where
  ok := com_ok mode
  inp := by
    rintro y ⟨u, rfl⟩ v hv
    have h3 : u.length + Lax434175.Results.maxEntry u + 2 ≤
        (u.length + Lax434175.Results.maxEntry u + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    simp only [List.tail_cons, bnd]
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at h3 ⊢
      omega
  run := by
    rintro y ⟨u, rfl⟩
    exact run_com mode u

open Lax759944.BinaryWordEncoding in
/-- The numbers of a word and its length are below `2 ^ (bitSize + 1)`. -/
theorem size_le (u : List ℕ) :
    u.length + Lax434175.Results.maxEntry u + 2 ≤ 2 ^ (bitSize u + 1) := by
  have h1 := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
  have h2 := Lax434175Proofs.ResultTransfer.maxEntry_lt u
  have h3 : bitSize u < 2 ^ bitSize u := Nat.lt_two_pow_self
  rw [pow_succ]
  omega

open Lax759944.BinaryWordEncoding in
/--
---
conclusion: Lax434175.ThresholdWords.stepWord_polytime
---
The program `com` reads the word into an array and writes the rows with the new
due dates and the new threshold, all in one pass: `O(|u|)` operations on numbers
of `O(log)` bits.
-/
theorem stepWord_polytime (mode : StepMode) :
    Lax759944.RamPolytime.RamPolytime (stepWord mode) := by
  refine (Lax496464.WH_A5_Bridges.polyTimeOn_univ_iff _).mp
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_runsTo (p := compileProgram layout (com mode))
      (c := 2001) (d := 1) (fun x _ w hw => ?_) (fun x _ v hv => ?_))
  · set b := bitSize x
    have hX : x.length + Lax434175.Results.maxEntry x + 2 ≤ 2 ^ (b + 1) := size_le x
    have hcube : (x.length + Lax434175.Results.maxEntry x + 2) ^ 3 ≤ 2 ^ ((b + 1) * 3) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hX 3
    have h8 : 2 ^ 3 ≤ 2 ^ ((b + 1) * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbig : bnd x + 23 ≤ 2 ^ ((b + 1) * 3 + 3) := by
      rw [pow_add]; unfold bnd; omega
    have hw' : 2 ^ ((b + 1) * 3 + 3) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by norm_num) (by rw [pow_one] at hw; omega)
    have hsol : Solves layout (com mode) {x.length :: x} (fun y => stepWord mode y.tail)
        (fun y => bnd y.tail) (fun y => cost y.tail) :=
      ⟨(solves mode).ok, fun y hy => (solves mode).inp y (by rw [Set.mem_singleton_iff.mp hy]; exact ⟨x, rfl⟩),
        fun y hy => (solves mode).run y (by rw [Set.mem_singleton_iff.mp hy]; exact ⟨x, rfl⟩)⟩
    have hc := computesInTime_of_solves (T := fun _ => 2001 * (b + 1) ^ 1) (w := w) hsol
      (fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        refine fitsWords_of_max_le ?_ ?_
        · simp only [List.tail_cons, bnd]
          have : 1 ≤ (x.length + Lax434175.Results.maxEntry x + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
          omega
        · simp only [List.tail_cons, Layout.span, layout, List.length_cons, List.length_nil]
          omega)
      (fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        have := Lax496464.WH_A4_MachineFacts.length_le_bitSize x
        simp only [List.tail_cons, cost, Layout.const, pow_one]
        omega)
    obtain ⟨t, ht, hrun⟩ := hc (x.length :: x) rfl
    exact ⟨t, ht, hrun⟩
  · set b := bitSize x
    have hX : x.length + Lax434175.Results.maxEntry x + 2 ≤ 2 ^ (b + 1) := size_le x
    have hv' := Lax434175Proofs.ThresholdWords.stepWord_le mode x v hv
    have hcube : (x.length + 1) * (Lax434175.Results.maxEntry x + 1) ^ 2 ≤ 2 ^ ((b + 1) * 3) := by
      have h1 : x.length + 1 ≤ 2 ^ (b + 1) := by omega
      have h2 : Lax434175.Results.maxEntry x + 1 ≤ 2 ^ (b + 1) := by omega
      calc (x.length + 1) * (Lax434175.Results.maxEntry x + 1) ^ 2
          ≤ 2 ^ (b + 1) * (2 ^ (b + 1)) ^ 2 := Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 2)
        _ = 2 ^ ((b + 1) * 3) := by ring
    have hlt : 2 ^ ((b + 1) * 3) < 2 ^ (2001 * (b + 1) ^ 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by rw [pow_one]; omega)
    omega

end Lax434175Proofs.ThresholdProgram
