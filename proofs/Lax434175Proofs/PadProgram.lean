import Mathlib.Tactic
import Lax808846Proofs.Transfer

/-!
The padding of an interval scheduling instance, as a word RAM program written in
IMP+: a job without an eligible machine gets the new machine `m` and weight `0`.
-/

namespace Lax434175Proofs.PadProgram

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer

/-! ### The Program -/

/-- `ctr < lim` -/
def below (ctr lim : String) : Cond := .lt (.var ctr) (.var lim)

/-- `ctr := ctr + 1` -/
def incr (ctr : String) : Com := .assign ctr (.add (.var ctr) (.lit 1))

/-- Copy the next `lim - ctr` numbers of the input to the output. -/
def copyLoop (ctr lim : String) : Com :=
  .while (below ctr lim) (.seq (.read "v") (.seq (.write (.var "v")) (incr ctr)))

/-- Read the next `lim` numbers of the input into the array `a`. -/
def readLoop (a lim : String) : Com :=
  .while (below "i" lim) (.seq (.read "v") (.seq (.store a (.var "i") (.var "v")) (incr "i")))

/-- `o[i] < o[i+1]`: the block of job `i` is not empty. -/
def nonempty : Cond := .lt (.get "o" (.var "i")) (.get "o" (.add (.var "i") (.lit 1)))

/-- The padded weights. -/
def weightLoop : Com :=
  .while (below "i" "n")
    (.seq (.ite nonempty (.write (.get "w" (.var "i"))) (.write (.lit 0))) (incr "i"))

/-- The offsets, shifted by the number of empty blocks before. -/
def offsetLoop : Com :=
  .while (below "i" "n")
    (.seq (.write (.add (.get "o" (.var "i")) (.var "e")))
      (.seq (.ite nonempty .skip (incr "e")) (incr "i")))

/-- The blocks of eligible machines, the new machine for an empty one. -/
def blockLoop : Com :=
  .while (below "i" "n")
    (.seq (.ite nonempty
        (.seq (.assign "k" (.get "o" (.var "i")))
          (.seq (.assign "h" (.get "o" (.add (.var "i") (.lit 1)))) (copyLoop "k" "h")))
        (.write (.var "m")))
      (incr "i"))

/-- `i := 0` -/
def reset : Com := .assign "i" (.lit 0)

/-- The whole program. -/
def com : Com :=
  .seq (.read "n") <| .seq (.read "m") <| .seq (.write (.var "n")) <|
  .seq (.write (.add (.var "m") (.lit 1))) <|
  .seq reset <| .seq (copyLoop "i" "n") <|
  .seq reset <| .seq (copyLoop "i" "n") <|
  .seq reset <| .seq (readLoop "w" "n") <|
  .seq (.assign "c" (.add (.var "n") (.lit 1))) <|
  .seq reset <| .seq (readLoop "o" "c") <|
  .seq reset <| .seq weightLoop <|
  .seq reset <| .seq (.assign "e" (.lit 0)) <| .seq offsetLoop <|
  .seq (.write (.add (.get "o" (.var "n")) (.var "e"))) <|
  .seq reset <| .seq blockLoop <|
  .seq (.read "v") (.write (.var "v"))

/-- The scalars, the two arrays, and three temporaries. -/
def layout : Layout := ⟨["n", "m", "i", "v", "c", "e", "k", "h"], ["w", "o"], 3⟩

/-- The machine program. -/
def prog : Program := compileProgram layout com

theorem com_ok : Com.Ok layout com := by
  simp [com, copyLoop, readLoop, weightLoop, offsetLoop, blockLoop, nonempty, below, incr,
    reset, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### Copying -/

/-- The copy loop moves a block of the input to the output, changing only the
counter and `v`. -/
theorem copy_run {B : ℕ} (ctr lim : String) (hcl : ctr ≠ lim) (hcv : ctr ≠ "v")
    (hlv : lim ≠ "v") (l rest : List ℕ) (τ : Env)
    (hlim : τ.vars lim = τ.vars ctr + l.length) (hinp : τ.inp = l ++ rest)
    (hB : ∀ v ∈ l, v < B) (hlimB : τ.vars lim < B) :
    ∃ τ', Run B (copyLoop ctr lim) τ τ' (12 * l.length + 4) ∧ τ'.inp = rest ∧
      τ'.out = τ.out ++ l ∧ τ'.vars ctr = τ.vars lim ∧
      (∀ y, y ≠ ctr → y ≠ "v" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs := by
  let Inv : Env → Prop := fun σ => ∃ k ≤ l.length, σ.vars ctr = τ.vars ctr + k ∧
    σ.inp = l.drop k ++ rest ∧ σ.out = τ.out ++ l.take k ∧
    (∀ y, y ≠ ctr → y ≠ "v" → σ.vars y = τ.vars y) ∧ σ.arrs = τ.arrs
  have hstep : ∀ σ, Inv σ → (below ctr lim).evalB B σ = some true →
      ∃ σ', Run B (.seq (.read "v") (.seq (.write (.var "v")) (incr ctr))) σ σ' 8 ∧ Inv σ' ∧
        σ'.vars lim - σ'.vars ctr < σ.vars lim - σ.vars ctr := by
    rintro σ ⟨k, hk, hc, hi, ho, hfr, ha⟩ hcond
    have hlimσ : σ.vars lim = τ.vars lim := hfr lim (Ne.symm hcl) hlv
    have hlt : σ.vars ctr < σ.vars lim := by
      have h := hcond
      simp [below] at h
      exact h.2.2
    have hkl : k < l.length := by omega
    have hdrop : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hkl
    have hvB : l[k] < B := hB _ (List.getElem_mem hkl)
    refine ⟨_, Run.mono (Run.seq (Run.read (x := "v") (by rw [hi, hdrop]; rfl))
      (Run.seq (Run.write (e := .var "v") (v := l[k]) (by simp; exact hvB))
        (Run.assign (x := ctr) (e := .add (.var ctr) (.lit 1)) (v := σ.vars ctr + 1)
          (by simp [hcv]; omega)))) (by simp), ?_, ?_⟩
    · refine ⟨k + 1, hkl, by simp [hc]; omega, by simp, ?_, fun y hy hyv => ?_, by simp [ha]⟩
      · show σ.out ++ [l[k]] = τ.out ++ l.take (k + 1)
        rw [ho, List.take_add_one, List.getElem?_eq_getElem hkl]
        simp
      · simp [hy, hyv, hfr y hy hyv]
    · simp [hlimσ, hcl.symm, hlv]
      omega
  obtain ⟨σ', hrun, ⟨k, hk, hc, hi, ho, hfr, ha⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := below ctr lim) Inv (fun σ => σ.vars lim - σ.vars ctr) 8
      (fun σ ⟨k, hk, hc, _, _, hfr, _⟩ => evalB_condLt_vars (by rw [hc]; omega)
        (by rw [hfr lim (Ne.symm hcl) hlv]; exact hlimB))
      hstep ⟨0, Nat.zero_le _, by simp, by simp [hinp], by simp, fun _ _ _ => rfl, rfl⟩
  have hlimσ : σ'.vars lim = τ.vars lim := hfr lim (Ne.symm hcl) hlv
  have hnot : ¬ σ'.vars ctr < σ'.vars lim := by
    have h := hfalse
    simp [below] at h
    omega
  have hkeq : k = l.length := by omega
  subst hkeq
  refine ⟨σ', hrun.mono ?_, by simp [hi], by simp [ho], by omega, hfr, ha⟩
  simp [below]
  omega

/-! ### Reading into an array -/

/-- The read loop stores a block of the input into an array of zeros. -/
theorem read_run {B : ℕ} (a lim : String) (hli : lim ≠ "i") (hlv : lim ≠ "v")
    (l rest : List ℕ) (len : ℕ) (hlen : l.length ≤ len) (τ : Env)
    (hi0 : τ.vars "i" = 0) (hlim : τ.vars lim = l.length) (hinp : τ.inp = l ++ rest)
    (ha : τ.arrs a = arrOf len (fun _ => 0))
    (hB : ∀ v ∈ l, v < B) (hlimB : l.length < B) :
    ∃ τ', Run B (readLoop a lim) τ τ' (13 * l.length + 4) ∧ τ'.inp = rest ∧
      τ'.out = τ.out ∧ τ'.vars "i" = l.length ∧
      (∀ y, y ≠ "i" → y ≠ "v" → τ'.vars y = τ.vars y) ∧
      τ'.arrs a = arrOf len (fun j => l.getD j 0) ∧ (∀ b, b ≠ a → τ'.arrs b = τ.arrs b) := by
  let Inv : Env → Prop := fun σ => ∃ k ≤ l.length, σ.vars "i" = k ∧
    σ.inp = l.drop k ++ rest ∧ σ.out = τ.out ∧
    (∀ y, y ≠ "i" → y ≠ "v" → σ.vars y = τ.vars y) ∧
    σ.arrs a = arrOf len (fun j => if j < k then l.getD j 0 else 0) ∧
    (∀ b, b ≠ a → σ.arrs b = τ.arrs b)
  have hstep : ∀ σ, Inv σ → (below "i" lim).evalB B σ = some true →
      ∃ σ', Run B (.seq (.read "v") (.seq (.store a (.var "i") (.var "v")) (incr "i"))) σ σ' 8 ∧
        Inv σ' ∧ σ'.vars lim - σ'.vars "i" < σ.vars lim - σ.vars "i" := by
    rintro σ ⟨k, hk, hc, hin, ho, hfr, harr, hoth⟩ hcond
    have hlimσ : σ.vars lim = l.length := (hfr lim hli hlv).trans hlim
    have hlt : σ.vars "i" < σ.vars lim := by
      have h := hcond
      simp [below] at h
      exact h.2.2
    have hkl : k < l.length := by omega
    have hdrop : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hkl
    have hvB : l[k] < B := hB _ (List.getElem_mem hkl)
    refine ⟨_, Run.mono (Run.seq (Run.read (x := "v") (by rw [hin, hdrop]; rfl))
      (Run.seq (Run.store (a := a) (i := .var "i") (e := .var "v") (idx := k) (v := l[k])
          (by simp; omega) (by simp; exact hvB) (by simp [harr]; omega))
        (Run.assign (x := "i") (e := .add (.var "i") (.lit 1)) (v := k + 1)
          (by simp [Env.setArr]; omega)))) (by simp), ?_, ?_⟩
    · refine ⟨k + 1, hkl, by simp, by simp, by simp [ho], fun y hy hyv => ?_, ?_,
        fun b hb => ?_⟩
      · simp [hy, hyv, hfr y hy hyv]
      · simp only [arrs_setVar, arrs_setArr, if_true]
        rw [harr, set_arrOf]
        refine arrOf_congr fun j _ => ?_
        by_cases hj : j = k
        · subst hj
          simp [List.getD_eq_getElem?_getD, hkl]
        · have : (j < k + 1) = (j < k) := by
            apply propext
            omega
          simp [hj, this]
      · simp [hb, hoth b hb]
    · simp [hlimσ, hli, hlv]
      omega
  obtain ⟨σ', hrun, ⟨k, hk, hc, hin, ho, hfr, harr, hoth⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := below "i" lim) Inv (fun σ => σ.vars lim - σ.vars "i") 8
      (fun σ ⟨k, hk, hc, _, _, hfr, _, _⟩ => evalB_condLt_vars (by rw [hc]; omega)
        (by rw [hfr lim hli hlv]; omega))
      hstep ⟨0, Nat.zero_le _, hi0, by simp [hinp], rfl, fun _ _ _ => rfl,
        by rw [ha]; exact arrOf_congr fun j _ => by simp, fun _ _ => rfl⟩
  have hlimσ : σ'.vars lim = l.length := (hfr lim hli hlv).trans hlim
  have hnot : ¬ σ'.vars "i" < σ'.vars lim := by
    have h := hfalse
    simp [below] at h
    omega
  have hkeq : k = l.length := by omega
  subst hkeq
  refine ⟨σ', hrun.mono ?_, by simp [hin], ho, hc, hfr, ?_, hoth⟩
  · simp [below, hi0, hlim]
    omega
  · rw [harr]
    refine arrOf_congr fun j hj => ?_
    by_cases hjl : j < l.length
    · simp [hjl]
    · simp [hjl, List.getD_eq_getElem?_getD]

/-! ### The padded weights -/

/-- Whether the block of job `j` is nonempty, for offsets `os`. -/
def full (os : ℕ → ℕ) (j : ℕ) : Prop := os j < os (j + 1)

instance (os : ℕ → ℕ) (j : ℕ) : Decidable (full os j) := inferInstanceAs (Decidable (_ < _))

theorem weight_run {B n : ℕ} (os ws : ℕ → ℕ) (τ : Env)
    (hi0 : τ.vars "i" = 0) (hn : τ.vars "n" = n)
    (ho : τ.arrs "o" = arrOf (n + 1) os) (hw : τ.arrs "w" = arrOf n ws)
    (hosB : ∀ j ≤ n, os j < B) (hwB : ∀ j < n, ws j < B) (hnB : n + 1 < B) :
    ∃ τ', Run B weightLoop τ τ' (20 * n + 4) ∧
      τ'.out = τ.out ++ (List.range n).map (fun j => if full os j then ws j else 0) ∧
      τ'.inp = τ.inp ∧ τ'.arrs = τ.arrs ∧ τ'.vars "i" = n ∧
      (∀ y, y ≠ "i" → τ'.vars y = τ.vars y) := by
  let Inv : Env → Prop := fun σ => ∃ k ≤ n, σ.vars "i" = k ∧
    σ.out = τ.out ++ (List.range k).map (fun j => if full os j then ws j else 0) ∧
    σ.inp = τ.inp ∧ σ.arrs = τ.arrs ∧ (∀ y, y ≠ "i" → σ.vars y = τ.vars y)
  have hstep : ∀ σ, Inv σ → (below "i" "n").evalB B σ = some true →
      ∃ σ', Run B (.seq (.ite nonempty (.write (.get "w" (.var "i"))) (.write (.lit 0)))
          (incr "i")) σ σ' 16 ∧
        Inv σ' ∧ σ'.vars "n" - σ'.vars "i" < σ.vars "n" - σ.vars "i" := by
    rintro σ ⟨k, hk, hc, ho', hin, harr, hfr⟩ hcond
    have hnσ : σ.vars "n" = n := (hfr "n" (by decide)).trans hn
    have hlt : k < n := by
      have h := hcond
      simp [below] at h
      omega
    have hok : (σ.arrs "o")[k]? = some (os k) := by
      rw [harr, ho]; exact getElem?_arrOf os (by omega)
    have hok1 : (σ.arrs "o")[k + 1]? = some (os (k + 1)) := by
      rw [harr, ho]; exact getElem?_arrOf os (by omega)
    have hwk : (σ.arrs "w")[k]? = some (ws k) := by
      rw [harr, hw]; exact getElem?_arrOf ws hlt
    have hcond' : nonempty.evalB B σ = some (decide (os k < os (k + 1))) :=
      evalB_condLt (evalB_get (evalB_var (by rw [hc]; omega)) (by rw [hc]; exact hok)
          (hosB k (by omega)))
        (evalB_get (evalB_bin (evalB_var (by rw [hc]; omega)) (evalB_lit (by omega))
            (by simp [hc]; omega)) (by simpa [hc] using hok1) (hosB (k + 1) (by omega)))
    by_cases hf : full os k
    · refine ⟨_, Run.mono (Run.seq
        (Run.ite_true (by rw [hcond']; simpa [full] using hf)
          (Run.write (e := .get "w" (.var "i")) (v := ws k)
            (evalB_get (evalB_var (by rw [hc]; omega)) (by rw [hc]; exact hwk) (hwB k hlt))))
        (Run.assign (x := "i") (e := .add (.var "i") (.lit 1)) (v := k + 1)
          (by simp [hc]; omega))) (by simp [nonempty]), ?_, ?_⟩
      · refine ⟨k + 1, hlt, by simp, ?_, by simp [hin], by simp [harr],
          fun y hy => by simp [hy, hfr y hy]⟩
        simp [ho', List.range_succ, hf]
      · simp [hnσ, hc]
        omega
    · refine ⟨_, Run.mono (Run.seq
        (Run.ite_false (by rw [hcond']; simpa [full] using hf)
          (Run.write (e := .lit 0) (v := 0) (evalB_lit (by omega))))
        (Run.assign (x := "i") (e := .add (.var "i") (.lit 1)) (v := k + 1)
          (by simp [hc]; omega))) (by simp [nonempty]), ?_, ?_⟩
      · refine ⟨k + 1, hlt, by simp, ?_, by simp [hin], by simp [harr],
          fun y hy => by simp [hy, hfr y hy]⟩
        simp [ho', List.range_succ, hf]
      · simp [hnσ, hc]
        omega
  obtain ⟨σ', hrun, ⟨k, hk, hc, ho', hin, harr, hfr⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := below "i" "n") Inv (fun σ => σ.vars "n" - σ.vars "i") 16
      (fun σ ⟨k, hk, hc, _, _, _, hfr⟩ => evalB_condLt_vars (by rw [hc]; omega)
        (by rw [hfr "n" (by decide), hn]; omega))
      hstep ⟨0, Nat.zero_le _, hi0, by simp, rfl, rfl, fun _ _ => rfl⟩
  have hnσ : σ'.vars "n" = n := (hfr "n" (by decide)).trans hn
  have hkeq : k = n := by
    have h := hfalse
    simp [below] at h
    omega
  subst hkeq
  exact ⟨σ', hrun.mono (by simp [below, hi0, hn]), ho', hin, harr, hc, hfr⟩

/-! ### The shifted offsets -/

/-- The number of empty blocks among the first `j` jobs. -/
def empties (os : ℕ → ℕ) (j : ℕ) : ℕ := ((List.range j).filter (fun i => ¬ full os i)).length

theorem empties_succ (os : ℕ → ℕ) (j : ℕ) :
    empties os (j + 1) = empties os j + (if full os j then 0 else 1) := by
  unfold empties
  rw [List.range_succ, List.filter_append]
  by_cases h : full os j <;> simp [h]

theorem empties_le (os : ℕ → ℕ) (j : ℕ) : empties os j ≤ j := by
  unfold empties
  exact (List.length_filter_le _ _).trans (by simp)

theorem offset_run {B n : ℕ} (os : ℕ → ℕ) (τ : Env)
    (hi0 : τ.vars "i" = 0) (he0 : τ.vars "e" = 0) (hn : τ.vars "n" = n)
    (ho : τ.arrs "o" = arrOf (n + 1) os) (hosB : ∀ j ≤ n, os j + n < B) (hnB : n + 1 < B) :
    ∃ τ', Run B offsetLoop τ τ' (26 * n + 4) ∧
      τ'.out = τ.out ++ (List.range n).map (fun j => os j + empties os j) ∧
      τ'.vars "e" = empties os n ∧ τ'.vars "i" = n ∧
      τ'.inp = τ.inp ∧ τ'.arrs = τ.arrs ∧
      (∀ y, y ≠ "i" → y ≠ "e" → τ'.vars y = τ.vars y) := by
  let Inv : Env → Prop := fun σ => ∃ k ≤ n, σ.vars "i" = k ∧ σ.vars "e" = empties os k ∧
    σ.out = τ.out ++ (List.range k).map (fun j => os j + empties os j) ∧
    σ.inp = τ.inp ∧ σ.arrs = τ.arrs ∧ (∀ y, y ≠ "i" → y ≠ "e" → σ.vars y = τ.vars y)
  have hstep : ∀ σ, Inv σ → (below "i" "n").evalB B σ = some true →
      ∃ σ', Run B (.seq (.write (.add (.get "o" (.var "i")) (.var "e")))
          (.seq (.ite nonempty .skip (incr "e")) (incr "i"))) σ σ' 22 ∧
        Inv σ' ∧ σ'.vars "n" - σ'.vars "i" < σ.vars "n" - σ.vars "i" := by
    rintro σ ⟨k, hk, hc, he, ho', hin, harr, hfr⟩ hcond
    have hnσ : σ.vars "n" = n := (hfr "n" (by decide) (by decide)).trans hn
    have hlt : k < n := by
      have h := hcond
      simp [below] at h
      omega
    have hok : (σ.arrs "o")[k]? = some (os k) := by
      rw [harr, ho]; exact getElem?_arrOf os (by omega)
    have hok1 : (σ.arrs "o")[k + 1]? = some (os (k + 1)) := by
      rw [harr, ho]; exact getElem?_arrOf os (by omega)
    have hek := empties_le os k
    have hB1 := hosB k (by omega)
    have hB2 := hosB (k + 1) (by omega)
    have hget : (Expr.get "o" (.var "i")).evalB B σ = some (os k) :=
      evalB_get (evalB_var (by rw [hc]; omega)) (by rw [hc]; exact hok) (by omega)
    have hcond' : nonempty.evalB B σ = some (decide (os k < os (k + 1))) :=
      evalB_condLt hget
        (evalB_get (evalB_bin (evalB_var (by rw [hc]; omega)) (evalB_lit (by omega))
            (by simp [hc]; omega)) (by simpa [hc] using hok1) (by omega))
    have hwrite : Run B (.write (.add (.get "o" (.var "i")) (.var "e"))) σ
        { σ with out := σ.out ++ [os k + empties os k] } 5 := by
      have := Run.write (B := B) (σ := σ) (e := .add (.get "o" (.var "i")) (.var "e"))
        (v := os k + empties os k)
        (by rw [← he]; exact evalB_bin hget (evalB_var (by rw [he]; omega)) (by simp; omega))
      simpa using this
    have hcondW : nonempty.evalB B { σ with out := σ.out ++ [os k + empties os k] } =
        some (decide (os k < os (k + 1))) := hcond'
    by_cases hf : full os k
    · refine ⟨_, Run.mono (Run.seq hwrite (Run.seq
        (Run.ite_true (by rw [hcondW]; simpa [full] using hf) Run.skip)
        (Run.assign (x := "i") (e := .add (.var "i") (.lit 1)) (v := k + 1)
          (by simp [hc]; omega)))) (by simp [nonempty]), ?_, ?_⟩
      · refine ⟨k + 1, hlt, by simp, ?_, ?_, by simp [hin], by simp [harr],
          fun y hy hye => by simp [hy, hfr y hy hye]⟩
        · simp [he, empties_succ, hf]
        · simp [ho', List.range_succ]
      · simp [hnσ, hc]
        omega
    · refine ⟨_, Run.mono (Run.seq hwrite (Run.seq
        (Run.ite_false (by rw [hcondW]; simpa [full] using hf)
          (Run.assign (x := "e") (e := .add (.var "e") (.lit 1)) (v := empties os k + 1)
            (by simp [he]; omega)))
        (Run.assign (x := "i") (e := .add (.var "i") (.lit 1)) (v := k + 1)
          (by simp [hc]; omega)))) (by simp [nonempty]), ?_, ?_⟩
      · refine ⟨k + 1, hlt, by simp, ?_, ?_, by simp [hin], by simp [harr],
          fun y hy hye => by simp [hy, hye, hfr y hy hye]⟩
        · simp [empties_succ, hf]
        · simp [ho', List.range_succ]
      · simp [hnσ, hc]
        omega
  obtain ⟨σ', hrun, ⟨k, hk, hc, he, ho', hin, harr, hfr⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := below "i" "n") Inv (fun σ => σ.vars "n" - σ.vars "i") 22
      (fun σ ⟨k, hk, hc, _, _, _, _, hfr⟩ => evalB_condLt_vars (by rw [hc]; omega)
        (by rw [hfr "n" (by decide) (by decide), hn]; omega))
      hstep ⟨0, Nat.zero_le _, hi0, by simp [he0, empties], by simp, rfl, rfl, fun _ _ _ => rfl⟩
  have hkeq : k = n := by
    have h := hfalse
    simp [below] at h
    have := (hfr "n" (by decide) (by decide)).trans hn
    omega
  subst hkeq
  exact ⟨σ', hrun.mono (by simp [below, hi0, hn]), ho', he, hc, hin, harr, hfr⟩

/-! ### The blocks -/

/-- The block of job `j` in the output: its eligible machines, or the new
machine `m` if it has none. -/
def blk (os : ℕ → ℕ) (ts : List ℕ) (m j : ℕ) : List ℕ :=
  if full os j then (ts.drop (os j)).take (os (j + 1) - os j) else [m]

theorem drop_split (ts : List ℕ) {a b : ℕ} (hab : a ≤ b) :
    ts.drop a = (ts.drop a).take (b - a) ++ ts.drop b := by
  conv_lhs => rw [← List.take_append_drop (b - a) (ts.drop a)]
  rw [List.drop_drop]
  congr 2
  omega

theorem block_run {B n m : ℕ} (os : ℕ → ℕ) (ts rest : List ℕ) (τ : Env)
    (hmono : ∀ j < n, os j ≤ os (j + 1)) (hlast : os n = ts.length) (hfirst : os 0 = 0)
    (hi0 : τ.vars "i" = 0) (hn : τ.vars "n" = n) (hm : τ.vars "m" = m)
    (ho : τ.arrs "o" = arrOf (n + 1) os) (hinp : τ.inp = ts ++ rest)
    (hosB : ∀ j ≤ n, os j < B) (htsB : ∀ v ∈ ts, v < B) (hnB : n + 1 < B) (hmB : m < B) :
    ∃ τ' K, Run B blockLoop τ τ' K ∧ K ≤ 40 * n + 12 * ts.length + 4 ∧
      τ'.out = τ.out ++ (List.range n).flatMap (blk os ts m) ∧ τ'.inp = rest ∧
      τ'.arrs = τ.arrs ∧ τ'.vars "n" = n := by
  let Inv : Env → Prop := fun σ => ∃ k ≤ n, σ.vars "i" = k ∧ σ.inp = ts.drop (os k) ++ rest ∧
    σ.out = τ.out ++ (List.range k).flatMap (blk os ts m) ∧ σ.arrs = τ.arrs ∧
    (∀ y, y ≠ "i" → y ≠ "k" → y ≠ "h" → y ≠ "v" → σ.vars y = τ.vars y)
  let Φ : Env → ℕ := fun σ => 40 * (n - σ.vars "i") + 12 * (os n - os (σ.vars "i"))
  have hmono' : ∀ a b, a ≤ b → b ≤ n → os a ≤ os b := by
    intro a b hab hbn
    induction b with
    | zero => rw [Nat.le_zero.mp hab]
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · rw [h]
      · exact (ih (by omega) (by omega)).trans (hmono b (by omega))
  have hstep : ∀ σ, Inv σ → (below "i" "n").evalB B σ = some true →
      ∃ σ' K, Run B (.seq (.ite nonempty
          (.seq (.assign "k" (.get "o" (.var "i")))
            (.seq (.assign "h" (.get "o" (.add (.var "i") (.lit 1)))) (copyLoop "k" "h")))
          (.write (.var "m"))) (incr "i")) σ σ' K ∧ Inv σ' ∧
        1 + (below "i" "n").size + K + Φ σ' ≤ Φ σ := by
    rintro σ ⟨k, hk, hc, hin, ho', harr, hfr⟩ hcond
    have hnσ : σ.vars "n" = n := (hfr "n" (by decide) (by decide) (by decide) (by decide)).trans hn
    have hmσ : σ.vars "m" = m := (hfr "m" (by decide) (by decide) (by decide) (by decide)).trans hm
    have hlt : k < n := by
      have h := hcond
      simp [below] at h
      omega
    have hok : (σ.arrs "o")[k]? = some (os k) := by
      rw [harr, ho]; exact getElem?_arrOf os (by omega)
    have hok1 : (σ.arrs "o")[k + 1]? = some (os (k + 1)) := by
      rw [harr, ho]; exact getElem?_arrOf os (by omega)
    have hB1 := hosB k (by omega)
    have hB2 := hosB (k + 1) (by omega)
    have hget : (Expr.get "o" (.var "i")).evalB B σ = some (os k) :=
      evalB_get (evalB_var (by rw [hc]; omega)) (by rw [hc]; exact hok) hB1
    have hcond' : nonempty.evalB B σ = some (decide (os k < os (k + 1))) :=
      evalB_condLt hget
        (evalB_get (evalB_bin (evalB_var (by rw [hc]; omega)) (evalB_lit (by omega))
            (by simp [hc]; omega)) (by simpa [hc] using hok1) hB2)
    have hle : os k ≤ os (k + 1) := hmono k hlt
    have hlen : os (k + 1) ≤ ts.length := hlast ▸ hmono' (k + 1) n (by omega) le_rfl
    by_cases hf : full os k
    · -- copy the block
      set σ1 := (σ.setVar "k" (os k)) with hσ1
      set σ2 := (σ1.setVar "h" (os (k + 1))) with hσ2
      have h2 : (Expr.get "o" (.add (.var "i") (.lit 1))).evalB B σ1 = some (os (k + 1)) := by
        refine evalB_get (evalB_bin (evalB_var (by simp [hσ1, hc]; omega)) (evalB_lit (by omega))
          (by simp [hσ1, hc]; omega)) ?_ hB2
        simpa [hσ1, hc] using hok1
      have hlenl : ((ts.drop (os k)).take (os (k + 1) - os k)).length = os (k + 1) - os k := by
        simp; omega
      obtain ⟨σ3, hcopy, hinp3, hout3, _, hfr3, harr3⟩ :=
        copy_run (B := B) "k" "h" (by decide) (by decide) (by decide)
          ((ts.drop (os k)).take (os (k + 1) - os k)) (ts.drop (os (k + 1)) ++ rest) σ2
          (by simp [hσ2, hσ1]; omega)
          (by simp [hσ2, hσ1, hin]; rw [← List.append_assoc, ← drop_split ts hle])
          (fun v hv => htsB v (List.mem_of_mem_drop (List.mem_of_mem_take hv)))
          (by simp [hσ2]; exact hB2)
      have hi3 : σ3.vars "i" = k := by
        rw [hfr3 "i" (by decide) (by decide)]; simp [hσ2, hσ1, hc]
      refine ⟨_, _, Run.seq (Run.ite_true (by rw [hcond']; simpa [full] using hf)
          (Run.seq (Run.assign (x := "k") (v := os k) hget)
            (Run.seq (Run.assign (x := "h") (v := os (k + 1)) h2) hcopy)))
        (Run.assign (x := "i") (e := .add (.var "i") (.lit 1)) (v := k + 1)
          (by simp [hi3]; omega)), ?_, ?_⟩
      · refine ⟨k + 1, hlt, by simp, by simp [hinp3], ?_, by simp [harr3, hσ2, hσ1, harr],
          fun y hy hyk hyh hyv => ?_⟩
        · simp [hout3, hσ2, hσ1, ho', List.range_succ, blk, hf]
        · simp [hy, hfr3 y hyk hyv, hσ2, hσ1, hyk, hyh, hfr y hy hyk hyh hyv]
      · have e1 : Φ (σ3.setVar "i" (k + 1)) = 40 * (n - (k + 1)) + 12 * (os n - os (k + 1)) := by
          simp [Φ]
        have e2 : Φ σ = 40 * (n - k) + 12 * (os n - os k) := by simp [Φ, hc]
        have hkn := hmono' (k + 1) n (by omega) le_rfl
        rw [e1, e2]
        simp only [below, size_condLt, size_var, nonempty, size_get, size_add, size_lit]
        omega
    · -- the new machine
      have heq : os (k + 1) = os k := by unfold full at hf; omega
      refine ⟨_, _, Run.seq (Run.ite_false (by rw [hcond']; simpa [full] using hf)
          (Run.write (e := .var "m") (v := m) (by simp [hmσ]; exact hmB)))
        (Run.assign (x := "i") (e := .add (.var "i") (.lit 1)) (v := k + 1)
          (by simp [hc]; omega)), ?_, ?_⟩
      · refine ⟨k + 1, hlt, by simp, by simp [hin, heq], ?_, by simp [harr],
          fun y hy hyk hyh hyv => by simp [hy, hfr y hy hyk hyh hyv]⟩
        simp [ho', List.range_succ, blk, hf]
      · have e1 : Φ ({ σ with out := σ.out ++ [m] }.setVar "i" (k + 1)) =
            40 * (n - (k + 1)) + 12 * (os n - os (k + 1)) := by simp [Φ]
        have e2 : Φ σ = 40 * (n - k) + 12 * (os n - os k) := by simp [Φ, hc]
        rw [e1, e2, heq]
        simp only [below, size_condLt, size_var, nonempty, size_get, size_add, size_lit]
        omega
  obtain ⟨σ', K, hrun, ⟨k, hk, hc, hin, ho', harr, hfr⟩, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := below "i" "n") Inv Φ
      (fun σ ⟨k, hk, hc, _, _, _, hfr⟩ => evalB_condLt_vars (by rw [hc]; omega)
        (by rw [hfr "n" (by decide) (by decide) (by decide) (by decide), hn]; omega))
      hstep ⟨0, Nat.zero_le _, hi0, by simp [hfirst, hinp], by simp, rfl,
        fun _ _ _ _ _ => rfl⟩
  have hnσ : σ'.vars "n" = n := (hfr "n" (by decide) (by decide) (by decide) (by decide)).trans hn
  have hkeq : k = n := by
    have h := hfalse
    simp [below] at h
    omega
  subst hkeq
  refine ⟨σ', K, hrun, ?_, ho', by simp [hin, hlast], harr, hnσ⟩
  simp [Φ, hi0, hc, below] at hpay
  rw [hfirst, hlast] at hpay
  omega

end Lax434175Proofs.PadProgram
