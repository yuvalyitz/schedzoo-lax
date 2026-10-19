import Mathlib.Tactic
import Lax434175Proofs.P200ProgramsSpec
import Lax434175Proofs.IsemPrograms

/-!
Writing the padded scaled instance (`buildWord`) as a word RAM program in IMP+: the program,
what stays fixed while it runs, and its pieces that compare two jobs (`sameCom`) and compute
the scale (`rCom`).
-/

namespace Lax434175Proofs.P200Programs
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost
open Lax434175Proofs.IsemPrograms (V incr prelude arrW run_prelude getD_le_max ev_rd minTo run_minTo
  upto store_upto upto_get)
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub)

local notation "mx" => Lax434175.Results.maxEntry

-- The program

/-- `dst := c_i`, the capped number of machines of job `i` (the index in `iv`). -/
def cOf (iv dst : String) : Com :=
  .seq (rdG "a" "L" "o1" (.add (.add (.add (.lit 3) (.mul (.lit 3) (V "n"))) (V iv)) (.lit 1))) <|
  .seq (rdG "a" "L" "o0" (.add (.add (.lit 3) (.mul (.lit 3) (V "n"))) (V iv))) <|
  .seq (.assign "dd" (.sub (V "o1") (V "o0"))) (minTo dst "dd" "L")

/-- `e := 0` unless the two values agree. -/
def test (e1 e2 : Expr) : Com := .ite (.eq e1 e2) .skip (.assign "e" (.lit 0))

/-- Compare the targets of jobs `j` and `k` at position `t`. -/
def cmpBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (.lit 4) (.mul (.lit 4) (V "n"))) (.add (V "oj") (V "t")))) <|
  .seq (rdG "a" "L" "w" (.add (.add (.lit 4) (.mul (.lit 4) (V "n"))) (.add (V "ok") (V "t")))) <|
  .seq (test (V "v") (V "w")) (incr "t")

/-- `e := 1` exactly when job `k` is a point with the due date and the machines of job `j`. -/
def sameCom : Com :=
  .seq (.assign "e" (.lit 1)) <|
  .seq (rdG "a" "L" "v" (.add (.lit 3) (V "k"))) <| .seq (test (V "v") (.lit 0)) <|
  .seq (rdG "a" "L" "v" (.add (.add (.lit 3) (V "n")) (V "k"))) <|
  .seq (rdG "a" "L" "w" (.add (.add (.lit 3) (V "n")) (V "j"))) <| .seq (test (V "v") (V "w")) <|
  .seq (cOf "j" "cj") <| .seq (cOf "k" "ck") <| .seq (test (V "cj") (V "ck")) <|
  .seq (rdG "a" "L" "oj" (.add (.add (.lit 3) (.mul (.lit 3) (V "n"))) (V "j"))) <|
  .seq (rdG "a" "L" "ok" (.add (.add (.lit 3) (.mul (.lit 3) (V "n"))) (V "k"))) <|
  forLoop "t" "cj" cmpBody

/-- `x := min (2 x) (n + 1)` -/
def dblBody : Com := .seq (.assign "y" (.add (V "x") (V "x"))) (.seq (minTo "x" "y" "n1") (incr "i"))

/-- `r := min (2 ^ min m n) n; K := 2 r + 3` -/
def rCom : Com :=
  .seq (.assign "x" (.lit 1)) <| .seq (minTo "mm" "m" "n") <|
  .seq (.assign "n1" (.add (V "n") (.lit 1))) <| .seq (forLoop "i" "mm" dblBody) <|
  .seq (minTo "r" "x" "n") (.assign "K" (.add (.mul (.lit 2) (V "r")) (.lit 3)))

/-- The flags of job `j`: real, head. -/
def flagBody : Com :=
  .seq (rdG "a" "L" "p" (.add (.lit 3) (V "j"))) <|
  .seq (rdG "a" "L" "d" (.add (.add (.lit 3) (V "n")) (V "j"))) <|
  .seq (.assign "z" (.lit 0)) <|
  .seq (.ite (.lt (.lit 0) (V "p")) (.ite (.lt (V "p") (.add (V "d") (.lit 1))) (.assign "z" (.lit 1)) .skip)
    .skip) <|
  .seq (.store "rl" (V "j") (V "z")) <|
  .seq (.assign "f" (.lit 1)) <|
  .seq (forLoop "k" "j" (.seq sameCom (.seq (.ite (.eq (V "e") (.lit 1)) (.assign "f" (.lit 0)) .skip)
    (incr "k")))) <|
  .seq (.ite (.eq (V "p") (.lit 0)) .skip (.assign "f" (.lit 0))) <|
  .seq (.store "hf" (V "j") (V "f")) (incr "j")

/-- `write p'_j` -/
def pOutBody : Com :=
  .seq (.ite (.eq (.get "rl" (V "j")) (.lit 1))
    (.seq (rdG "a" "L" "p" (.add (.lit 3) (V "j")))
      (.write (.sub (.sub (.mul (V "K") (V "p")) (.mul (.lit 2) (V "r"))) (.lit 2))))
    (.write (.lit 1))) (incr "j")

/-- `s += 1` for an earlier head with the same due date -/
def slotBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (.lit 3) (V "n")) (V "k"))) <|
  .seq (.ite (.eq (.get "hf" (V "k")) (.lit 1))
    (.ite (.eq (V "v") (V "d")) (.assign "s" (.add (V "s") (.lit 1))) .skip) .skip) (incr "k")

/-- `write d'_j` -/
def dOutBody : Com :=
  .seq (rdG "a" "L" "d" (.add (.add (.lit 3) (V "n")) (V "j"))) <|
  .seq (.ite (.eq (.get "rl" (V "j")) (.lit 1))
    (.write (.sub (.sub (.mul (V "K") (V "d")) (V "r")) (.lit 1)))
    (.ite (.eq (.get "hf" (V "j")) (.lit 1))
      (.seq (.assign "s" (.lit 0)) (.seq (forLoop "k" "j" slotBody)
        (.write (.add (.add (.mul (V "K") (V "d")) (V "s")) (.lit 1)))))
      (.write (.lit 1)))) (incr "j")

/-- `s += w_k` for a point of the kind of job `j` -/
def hwBody : Com :=
  .seq sameCom <|
  .seq (.ite (.eq (V "e") (.lit 1))
    (.seq (rdG "a" "L" "v" (.add (.add (.lit 3) (.mul (.lit 2) (V "n"))) (V "k")))
      (.assign "s" (.add (V "s") (V "v")))) .skip) (incr "k")

/-- `write w'_j` -/
def wOutBody : Com :=
  .seq (.ite (.eq (.get "rl" (V "j")) (.lit 1))
    (.seq (rdG "a" "L" "v" (.add (.add (.lit 3) (.mul (.lit 2) (V "n"))) (V "j"))) (.write (V "v")))
    (.ite (.eq (.get "hf" (V "j")) (.lit 1))
      (.seq (.assign "s" (.lit 0)) (.seq (forLoop "k" "n" hwBody) (.write (V "s"))))
      (.write (.lit 0)))) (incr "j")

/-- The job is kept: real or a head. -/
def keepC : Cond := .lt (.lit 0) (.add (.get "rl" (V "j")) (.get "hf" (V "j")))

/-- `s += |block_j|; write s` -/
def offBodyB : Com :=
  .seq (.ite keepC (.seq (cOf "j" "c") (.assign "s" (.add (V "s") (V "c"))))
    (.assign "s" (.add (V "s") (.lit 1)))) <|
  .seq (.write (V "s")) (incr "j")

/-- `write` a target -/
def tBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (.lit 4) (.mul (.lit 4) (V "n"))) (.add (V "o") (V "t")))) <|
  .seq (.write (V "v")) (incr "t")

/-- `write` the block of job `j` -/
def tgBodyB : Com :=
  .seq (.ite keepC
    (.seq (cOf "j" "c") (.seq (rdG "a" "L" "o" (.add (.add (.lit 3) (.mul (.lit 3) (V "n"))) (V "j")))
      (forLoop "t" "c" tBody)))
    (.write (V "m"))) (incr "j")

def bwCom : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 0)) <| .seq (minTo "n" "c" "L") <|
  .seq (rdG "a" "L" "m" (.lit 1)) <| .seq (rdG "a" "L" "W" (.lit 2)) <|
  .seq rCom <|
  .seq (forLoop "j" "n" flagBody) <|
  .seq (.write (V "n")) <|
  .seq (.ite (.lt (V "L") (.lit 4)) (.write (V "m")) (.write (.add (V "m") (.lit 1)))) <|
  .seq (forLoop "j" "n" pOutBody) <| .seq (forLoop "j" "n" dOutBody) <|
  .seq (forLoop "j" "n" wOutBody) <|
  .seq (.assign "s" (.lit 0)) <| .seq (.write (V "s")) <| .seq (forLoop "j" "n" offBodyB) <|
  .seq (forLoop "j" "n" tgBodyB) (.write (V "W"))

def bwLayout : Layout :=
  ⟨["L", "i", "v", "c", "n", "m", "W", "x", "mm", "n1", "y", "r", "K", "j", "p", "d", "z", "f", "k", "e",
    "w", "o1", "o0", "dd", "cj", "ck", "oj", "ok", "t", "s", "o"], ["a", "rl", "hf"], 6⟩

theorem bwCom_ok : Com.Ok bwLayout bwCom := by
  simp [bwCom, rCom, dblBody, flagBody, sameCom, cOf, test, cmpBody, pOutBody, slotBody, dOutBody,
    hwBody, wOutBody, keepC, offBodyB, tBody, tgBodyB, prelude, minTo, rdG,
    Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, bwLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

-- Bounds

theorem nB_le (x : List ℕ) : nB x ≤ x.length := min_le_right _ _
theorem cB_le (x : List ℕ) (j : ℕ) : cB x j ≤ x.length := min_le_right _ _
theorem rB_le (x : List ℕ) : rB x ≤ nB x := min_le_right _ _

/-- What the value bound must admit. -/
structure BB (x : List ℕ) (B : ℕ) : Prop where
  idx : 5 * x.length + mx x + 30 < B
  prod : (2 * x.length + 3) * mx x + 3 * x.length + 10 < B
  sum : x.length * mx x + x.length * (x.length + 1) + mx x + 10 < B

theorem bb_of {x : List ℕ} {B : ℕ} (hB : 8 * (x.length + mx x + 8) ^ 2 ≤ B) : BB x B :=
  ⟨by nlinarith, by nlinarith, by nlinarith⟩

section BW
variable {B : ℕ} {x : List ℕ}

theorem BB.M (b : BB x B) : mx x < B := by have := b.idx; omega
theorem BB.Lt (b : BB x B) : x.length < B := by have := b.idx; omega
theorem BB.g (b : BB x B) (i : ℕ) : x.getD i 0 < B := lt_of_le_of_lt (getD_le_max x i) b.M

/-- What stays fixed while writing. -/
structure BC (x : List ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = arrW x
  L : τ.vars "L" = x.length
  n : τ.vars "n" = nB x
  m : τ.vars "m" = mB x
  W : τ.vars "W" = WB x
  r : τ.vars "r" = rB x
  K : τ.vars "K" = KB x

/-- The names `BC` fixes. -/
abbrev fixedB : List String := ["L", "n", "m", "W", "r", "K"]

theorem BC.frame {τ τ' : Env} (h : BC x τ) (ha : τ'.arrs "a" = τ.arrs "a")
    (hv : ∀ y ∈ fixedB, τ'.vars y = τ.vars y) : BC x τ' :=
  ⟨by rw [ha, h.a], by rw [hv "L" (by simp), h.L], by rw [hv "n" (by simp), h.n],
    by rw [hv "m" (by simp), h.m], by rw [hv "W" (by simp), h.W], by rw [hv "r" (by simp), h.r],
    by rw [hv "K" (by simp), h.K]⟩

theorem BC.setVar {τ : Env} (h : BC x τ) {y : String} (hy : y ∉ fixedB) (w : ℕ) : BC x (τ.setVar y w) :=
  h.frame (by simp) (fun z hz => by simp only [vars_setVar]; rw [if_neg (fun e : z = y => hy (e ▸ hz))])

theorem BC.setArr {τ : Env} (h : BC x τ) {b : String} (hb : b ≠ "a") (i w : ℕ) : BC x (τ.setArr b i w) :=
  h.frame (by simp [hb.symm]) (fun z _ => by simp)

theorem BC.out {τ : Env} (h : BC x τ) (o : List ℕ) : BC x { τ with out := o } := h.frame rfl (fun _ _ => rfl)

/-- A run changes only the names in `S`, and neither the arrays nor the output. -/
def Fr (S : List String) (τ τ' : Env) : Prop :=
  τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ ∀ y, y ∉ S → τ'.vars y = τ.vars y

theorem Fr.rfl' {S : List String} {τ : Env} : Fr S τ τ := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Fr.setVar {S : List String} {τ τ' : Env} (h : Fr S τ τ') {y : String} (hy : y ∈ S) (w : ℕ) :
    Fr S τ (τ'.setVar y w) :=
  ⟨h.1, h.2.1, fun z hz => by simp only [vars_setVar]; rw [if_neg (fun e : z = y => hz (e ▸ hy)), h.2.2 z hz]⟩

theorem Fr.trans {S : List String} {τ τ' τ'' : Env} (h : Fr S τ τ') (h' : Fr S τ' τ'') : Fr S τ τ'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun z hz => (h'.2.2 z hz).trans (h.2.2 z hz)⟩

theorem Fr.mono {S S' : List String} {τ τ' : Env} (h : Fr S τ τ') (hS : ∀ y ∈ S, y ∈ S') : Fr S' τ τ' :=
  ⟨h.1, h.2.1, fun z hz => h.2.2 z (fun h' => hz (hS z h'))⟩

theorem BC.ofFr {S : List String} {τ τ' : Env} (h : BC x τ) (hf : Fr S τ τ') (hS : ∀ y ∈ fixedB, y ∉ S) :
    BC x τ' :=
  h.frame (by rw [hf.1]) (fun y hy => hf.2.2 y (hS y hy))

theorem run_incr {τ : Env} (z : String) {k : ℕ} (hx : τ.vars z = k) (hk : k + 1 < B) :
    Run B (incr z) τ (τ.setVar z (k + 1)) 4 :=
  (Run.assign (ev_add (ev_var hx (by omega)) (ev_lit (by omega)) hk)).mono (by simp)

/-- **A test.** -/
theorem run_test {e1 e2 : Expr} {τ : Env} {v1 v2 : ℕ} (h1 : e1.evalB B τ = some v1)
    (h2 : e2.evalB B τ = some v2) (hB : 1 < B) {P : Bool} (he : τ.vars "e" = if P then 1 else 0) :
    ∃ τ', Run B (test e1 e2) τ τ' (e1.size + e2.size + 4) ∧ Fr ["e"] τ τ' ∧
      τ'.vars "e" = if (P && v1 == v2) then 1 else 0 := by
  have hc : (Cond.eq e1 e2).evalB B τ = some (v1 == v2) := evalB_condEq h1 h2
  by_cases hv : v1 = v2
  · refine ⟨τ, (Run.ite_true (by rw [hc]; simp [hv]) Run.skip).mono (by simp; omega), Fr.rfl', ?_⟩
    simp [he, hv]
  · refine ⟨_, (Run.ite_false (by rw [hc]; simp [hv]) (Run.assign (ev_lit (n := 0) (by omega)))).mono
      (by simp; omega), Fr.rfl'.setVar (by simp) 0, ?_⟩
    simp [hv]

/-- Reading `a[3 + q n + i]`. -/
theorem ev_at (bd : BB x B) {τ : Env} (h : BC x τ) (q : ℕ) (hq : q ≤ 4) {iv : String} {i : ℕ}
    (hi : τ.vars iv = i) (hiB : i ≤ x.length + mx x) :
    (Expr.add (.add (.lit 3) (.mul (.lit q) (V "n"))) (V iv)).evalB B τ = some (3 + q * nB x + i) := by
  have hn := nB_le x
  have := bd.idx
  have : q * nB x ≤ 4 * x.length := by nlinarith
  exact ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var h.n (by omega)) (by omega))
    (by omega)) (ev_var hi (by omega)) (by omega)

/-- **The number of machines of a job.** -/
theorem run_cOf (bd : BB x B) {τ : Env} (h : BC x τ) {iv dst : String} {i : ℕ} (hi : τ.vars iv = i)
    (hiB : i ≤ x.length) (h1 : iv ≠ "o1") (h2 : iv ≠ "o0") :
    ∃ τ', Run B (cOf iv dst) τ τ' 60 ∧ Fr ["o1", "o0", "dd", dst] τ τ' ∧ τ'.vars dst = cB x i := by
  have hn := nB_le x
  have hidx := bd.idx
  have i0 := ev_at bd h 3 (by norm_num) hi (by omega)
  have i1 : (Expr.add (.add (.add (.lit 3) (.mul (.lit 3) (V "n"))) (V iv)) (.lit 1)).evalB B τ =
      some (3 + 3 * nB x + i + 1) := ev_add i0 (ev_lit (by omega)) (by omega)
  have r1 := ev_rd h.a h.L i1 bd.M bd.Lt "o1"
  rw [show x.getD (3 + 3 * nB x + i + 1) 0 = oB x (i + 1) by unfold oB; congr 1] at r1
  set τ1 := τ.setVar "o1" (oB x (i + 1))
  have h1' : BC x τ1 := h.setVar (by simp) _
  have i0' := ev_at bd h1' 3 (by norm_num) (iv := iv) (i := i) (by simp [τ1, h1, hi]) (by omega)
  have r2 := ev_rd h1'.a h1'.L i0' bd.M bd.Lt "o0"
  rw [show x.getD (3 + 3 * nB x + i) 0 = oB x i from rfl] at r2
  set τ2 := τ1.setVar "o0" (oB x i)
  have r3 : Run B (.assign "dd" (.sub (V "o1") (V "o0"))) τ2 (τ2.setVar "dd" (oB x (i + 1) - oB x i)) 4 :=
    (Run.assign (ev_sub (ev_var (v := oB x (i + 1)) (by simp [τ2, τ1]) (bd.g _))
      (ev_var (v := oB x i) (by simp [τ2]) (bd.g _)))).mono (by simp)
  set τ3 := τ2.setVar "dd" (oB x (i + 1) - oB x i)
  have r4 : Run B (minTo dst "dd" "L") τ3 (τ3.setVar dst (cB x i)) 6 :=
    run_minTo (by simp [τ3]) (by simp [τ3, τ2, τ1, h.L]) (lt_of_le_of_lt (Nat.sub_le _ _) (bd.g _)) bd.Lt
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by simp), ?_, by simp⟩
  exact (((Fr.rfl'.setVar (by simp) _).setVar (by simp) _).setVar (by simp) _).setVar (by simp) _

/-- The temporaries of `sameCom`. -/
abbrev sameTemps : List String := ["e", "v", "w", "o1", "o0", "dd", "cj", "ck", "oj", "ok", "t"]

theorem oB_le (x : List ℕ) (i : ℕ) : oB x i ≤ mx x := getD_le_max x _

/-- **Comparing two jobs.** -/
theorem run_same (bd : BB x B) {τ : Env} (h : BC x τ) {j k : ℕ} (hj : τ.vars "j" = j) (hk : τ.vars "k" = k)
    (hjn : j < nB x) (hkn : k < nB x) :
    ∃ τ', Run B sameCom τ τ' (60 * x.length + 400) ∧ Fr sameTemps τ τ' ∧
      τ'.vars "e" = if sameB x j k then 1 else 0 := by
  have hn := nB_le x
  have hidx := bd.idx
  have hbc : ∀ σ, Fr sameTemps τ σ → BC x σ := fun σ hf => h.ofFr hf (by decide)
  have hjv : ∀ σ, Fr sameTemps τ σ → σ.vars "j" = j := fun σ hf => (hf.2.2 "j" (by decide)).trans hj
  have hkv : ∀ σ, Fr sameTemps τ σ → σ.vars "k" = k := fun σ hf => (hf.2.2 "k" (by decide)).trans hk
  -- e := 1
  set τ0 := τ.setVar "e" 1
  have f0 : Fr sameTemps τ τ0 := Fr.rfl'.setVar (by simp) _
  have r0 : Run B (.assign "e" (.lit 1)) τ τ0 2 := Run.assign (ev_lit (by omega))
  -- p_k = 0
  have r1 := ev_rd (hbc _ f0).a (hbc _ f0).L (e := .add (.lit 3) (V "k"))
    (ev_add (ev_lit (by omega)) (ev_var (hkv _ f0) (by omega)) (by omega)) bd.M bd.Lt "v"
  rw [show x.getD (3 + k) 0 = pB x k from rfl] at r1
  set τ1 := τ0.setVar "v" (pB x k)
  have f1 : Fr sameTemps τ τ1 := f0.setVar (by simp) _
  obtain ⟨τ2, r2, f2', he2⟩ := run_test (B := B) (τ := τ1) (P := true) (e1 := V "v") (e2 := .lit 0) (ev_var (v := pB x k) (by simp [τ1]) (bd.g _))
    (ev_lit (n := 0) (by omega)) (by omega) (by simp [τ1, τ0])
  have f2 : Fr sameTemps τ τ2 := f1.trans (f2'.mono (by simp))
  -- d_k = d_j
  have r3 := ev_rd (hbc _ f2).a (hbc _ f2).L (e := .add (.add (.lit 3) (V "n")) (V "k"))
    (ev_add (ev_add (ev_lit (by omega)) (ev_var (hbc _ f2).n (by omega)) (by omega))
      (ev_var (hkv _ f2) (by omega)) (by omega)) bd.M bd.Lt "v"
  rw [show x.getD (3 + nB x + k) 0 = dB x k from rfl] at r3
  set τ3 := τ2.setVar "v" (dB x k)
  have f3 : Fr sameTemps τ τ3 := f2.setVar (by simp) _
  have r4 := ev_rd (hbc _ f3).a (hbc _ f3).L (e := .add (.add (.lit 3) (V "n")) (V "j"))
    (ev_add (ev_add (ev_lit (by omega)) (ev_var (hbc _ f3).n (by omega)) (by omega))
      (ev_var (hjv _ f3) (by omega)) (by omega)) bd.M bd.Lt "w"
  rw [show x.getD (3 + nB x + j) 0 = dB x j from rfl] at r4
  set τ4 := τ3.setVar "w" (dB x j)
  have f4 : Fr sameTemps τ τ4 := f3.setVar (by simp) _
  obtain ⟨τ5, r5, f5', he5⟩ := run_test (B := B) (τ := τ4) (e1 := V "v") (e2 := V "w") (ev_var (v := dB x k) (by simp [τ4, τ3]) (bd.g _))
    (ev_var (v := dB x j) (by simp [τ4]) (bd.g _)) (by omega) (P := true && pB x k == 0)
    (by simp [τ4, τ3, he2])
  have f5 : Fr sameTemps τ τ5 := f4.trans (f5'.mono (by simp))
  -- c_j = c_k
  obtain ⟨τ6, r6, f6', hc6⟩ := run_cOf bd (hbc _ f5) (dst := "cj") (hjv _ f5) (by omega) (by decide) (by decide)
  have f6 : Fr sameTemps τ τ6 := f5.trans (f6'.mono (by simp))
  obtain ⟨τ7, r7, f7', hc7⟩ := run_cOf bd (hbc _ f6) (dst := "ck") (hkv _ f6) (by omega) (by decide) (by decide)
  have f7 : Fr sameTemps τ τ7 := f6.trans (f7'.mono (by simp))
  have hcj : τ7.vars "cj" = cB x j := by rw [f7'.2.2 "cj" (by decide), hc6]
  have hcjL := cB_le x j
  have hckL := cB_le x k
  obtain ⟨τ8, r8, f8', he8⟩ := run_test (B := B) (τ := τ7) (e1 := V "cj") (e2 := V "ck") (ev_var hcj (by omega)) (ev_var hc7 (by omega))
    (by omega) (P := (true && pB x k == 0) && dB x k == dB x j)
    (by rw [f7'.2.2 "e" (by decide), f6'.2.2 "e" (by decide), he5])
  have f8 : Fr sameTemps τ τ8 := f7.trans (f8'.mono (by simp))
  -- the offsets
  have r9 := ev_rd (hbc _ f8).a (hbc _ f8).L (ev_at bd (hbc _ f8) 3 (by norm_num) (hjv _ f8) (by omega))
    bd.M bd.Lt "oj"
  rw [show x.getD (3 + 3 * nB x + j) 0 = oB x j from rfl] at r9
  set τ9 := τ8.setVar "oj" (oB x j)
  have f9 : Fr sameTemps τ τ9 := f8.setVar (by simp) _
  have r10 := ev_rd (hbc _ f9).a (hbc _ f9).L (ev_at bd (hbc _ f9) 3 (by norm_num) (hkv _ f9) (by omega))
    bd.M bd.Lt "ok"
  rw [show x.getD (3 + 3 * nB x + k) 0 = oB x k from rfl] at r10
  set τ10 := τ9.setVar "ok" (oB x k)
  have f10 : Fr sameTemps τ τ10 := f9.setVar (by simp) _
  -- the targets
  set P0 : Bool := ((true && pB x k == 0) && dB x k == dB x j) && cB x j == cB x k
  have hoj := oB_le x j
  have hok := oB_le x k
  obtain ⟨τ11, r11, -, f11, -, -, -, he11⟩ := run_forLoop (B := B) "t" "cj" cmpBody (cB x j) 56 (by omega)
    (fun i σ => σ.vars "t" = i ∧ Fr sameTemps τ σ ∧ σ.vars "oj" = oB x j ∧ σ.vars "ok" = oB x k ∧
      σ.vars "cj" = cB x j ∧
      σ.vars "e" = if (P0 && (List.range i).all fun t => tB x (oB x j + t) == tB x (oB x k + t)) then 1 else 0)
    (fun i σ h => h.1) (fun i σ h => h.2.2.2.2.1)
    (fun i hi σ ⟨ht, hf, hoj', hok', hcj', he'⟩ => by
      have hb := hbc _ hf
      have ev1 : ∀ (σ' : Env) (ov : String) (o : ℕ), BC x σ' → σ'.vars "t" = i → σ'.vars ov = o → o ≤ mx x →
          (Expr.add (.add (.lit 4) (.mul (.lit 4) (V "n"))) (.add (V ov) (V "t"))).evalB B σ' =
            some (4 + 4 * nB x + (o + i)) := fun σ' ov o hb' ht' h1 h2 =>
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hb'.n (by omega)) (by omega))
          (by omega)) (ev_add (ev_var h1 (by omega)) (ev_var ht' (by omega)) (by omega)) (by omega)
      have q1 := ev_rd hb.a hb.L (ev1 σ "oj" _ hb ht hoj' hoj) bd.M bd.Lt "v"
      rw [show x.getD (4 + 4 * nB x + (oB x j + i)) 0 = tB x (oB x j + i) from rfl] at q1
      set σ1 := σ.setVar "v" (tB x (oB x j + i))
      have hb1 : BC x σ1 := hb.setVar (by decide) _
      have q2 := ev_rd hb1.a hb1.L (ev1 σ1 "ok" _ hb1 (by simp [σ1, ht]) (by simp [σ1, hok']) hok) bd.M bd.Lt "w"
      rw [show x.getD (4 + 4 * nB x + (oB x k + i)) 0 = tB x (oB x k + i) from rfl] at q2
      set σ2 := σ1.setVar "w" (tB x (oB x k + i))
      obtain ⟨σ3, q3, g3, he3⟩ := run_test (B := B) (τ := σ2) (e1 := V "v") (e2 := V "w") (ev_var (v := tB x (oB x j + i)) (by simp [σ2, σ1])
        (bd.g _)) (ev_var (v := tB x (oB x k + i)) (by simp [σ2]) (bd.g _)) (by omega)
        (P := P0 && (List.range i).all fun t => tB x (oB x j + t) == tB x (oB x k + t))
        (by simp only [σ2, σ1, vars_setVar]; exact he')
      have ht3 : σ3.vars "t" = i := by rw [g3.2.2 "t" (by decide)]; simp [σ2, σ1, ht]
      refine ⟨_, (q1.seq (q2.seq (q3.seq (run_incr "t" ht3 (by omega))))).mono (by simp), by simp, ?_, ?_,
        ?_, ?_, ?_⟩
      · exact ((hf.setVar (by simp) _).setVar (by simp) _).trans ((g3.mono (by simp)).setVar (by simp) _)
      · rw [show ((σ3.setVar "t" (i + 1)).vars "oj") = σ3.vars "oj" by simp, g3.2.2 "oj" (by decide)]
        simp [σ2, σ1, hoj']
      · rw [show ((σ3.setVar "t" (i + 1)).vars "ok") = σ3.vars "ok" by simp, g3.2.2 "ok" (by decide)]
        simp [σ2, σ1, hok']
      · rw [show ((σ3.setVar "t" (i + 1)).vars "cj") = σ3.vars "cj" by simp, g3.2.2 "cj" (by decide)]
        simp [σ2, σ1, hcj']
      · rw [show ((σ3.setVar "t" (i + 1)).vars "e") = σ3.vars "e" by simp, he3, List.range_succ,
          List.all_append]
        simp [Bool.and_assoc])
    (σ := τ10) ⟨by simp, f10.setVar (by simp) _, by simp [τ10, τ9], by simp [τ10],
      by simp [τ10, τ9, f8'.2.2 "cj" (by decide), hcj], by simp [τ10, τ9, he8, P0]⟩
  refine ⟨τ11, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    r11))))))))))).mono ?_, f11, ?_⟩
  · have : 56 * cB x j ≤ 56 * x.length := Nat.mul_le_mul_left _ hcjL
    simp only [Expr.size]
    omega
  · rw [he11]; unfold sameB; congr 1

theorem min_dbl (a N : ℕ) : min (2 * min a N) N = min (a * 2) N := by omega

/-- **The scale.** -/
theorem run_r (bd : BB x B) {τ : Env} (hn : τ.vars "n" = nB x) (hm : τ.vars "m" = mB x) :
    ∃ τ', Run B rCom τ τ' (18 * x.length + 40) ∧ Fr ["x", "mm", "n1", "i", "y", "r", "K"] τ τ' ∧
      τ'.vars "r" = rB x ∧ τ'.vars "K" = KB x := by
  have hnL := nB_le x
  have hidx := bd.idx
  have hmM : mB x ≤ mx x := getD_le_max x 1
  set τ0 := τ.setVar "x" 1
  have r0 : Run B (.assign "x" (.lit 1)) τ τ0 2 := Run.assign (ev_lit (by omega))
  have r1 : Run B (minTo "mm" "m" "n") τ0 (τ0.setVar "mm" (min (mB x) (nB x))) 6 :=
    run_minTo (by simp [τ0, hm]) (by simp [τ0, hn]) (by omega) (by omega)
  set τ1 := τ0.setVar "mm" (min (mB x) (nB x))
  have r2 : Run B (.assign "n1" (.add (V "n") (.lit 1))) τ1 (τ1.setVar "n1" (nB x + 1)) 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ1, τ0, hn]) (by omega)) (ev_lit (by omega)) (by omega))).mono
      (by simp)
  set τ2 := τ1.setVar "n1" (nB x + 1)
  have hmm : min (mB x) (nB x) ≤ x.length := by omega
  obtain ⟨τ3, r3, -, f3, hx3, hn3, hn13, -⟩ := run_forLoop (B := B) "i" "mm" dblBody (min (mB x) (nB x)) 14
    (by omega)
    (fun i σ => σ.vars "i" = i ∧ Fr ["x", "mm", "n1", "i", "y", "r", "K"] τ σ ∧
      σ.vars "x" = min (2 ^ i) (nB x + 1) ∧ σ.vars "n" = nB x ∧ σ.vars "n1" = nB x + 1 ∧
      σ.vars "mm" = min (mB x) (nB x))
    (fun i σ h => h.1) (fun i σ h => h.2.2.2.2.2)
    (fun i hi σ ⟨hiv, hf, hx, hnn, hn1, hmmv⟩ => by
      have hxl : min (2 ^ i) (nB x + 1) ≤ nB x + 1 := min_le_right _ _
      have q1 : Run B (.assign "y" (.add (V "x") (V "x"))) σ
          (σ.setVar "y" (min (2 ^ i) (nB x + 1) + min (2 ^ i) (nB x + 1))) 4 :=
        (Run.assign (ev_add (ev_var hx (by omega)) (ev_var hx (by omega)) (by omega))).mono (by simp)
      set σ1 := σ.setVar "y" (min (2 ^ i) (nB x + 1) + min (2 ^ i) (nB x + 1))
      have q2 : Run B (minTo "x" "y" "n1") σ1 (σ1.setVar "x" (min (2 ^ (i + 1)) (nB x + 1))) 6 := by
        have e : min (2 ^ (i + 1)) (nB x + 1) =
            min (min (2 ^ i) (nB x + 1) + min (2 ^ i) (nB x + 1)) (nB x + 1) := by
          rw [pow_succ]; omega
        rw [e]
        exact run_minTo (by simp [σ1]) (by simp [σ1, hn1]) (by omega) (by omega)
      set σ2 := σ1.setVar "x" (min (2 ^ (i + 1)) (nB x + 1))
      refine ⟨_, (q1.seq (q2.seq (run_incr "i" (k := i) (by simp [σ2, σ1, hiv]) (by omega)))).mono (by simp),
        by simp, ((hf.setVar (by simp) _).setVar (by simp) _).setVar (by simp) _, by simp [σ2],
        by simp [σ2, σ1, hnn], by simp [σ2, σ1, hn1], by simp [σ2, σ1, hmmv]⟩)
    (σ := τ2) ⟨by simp, ((((Fr.rfl'.setVar (by simp) _).setVar (by simp) _).setVar (by simp) _).setVar
      (by simp) _), by simp [τ2, τ1, τ0], by simp [τ2, τ1, τ0, hn], by simp [τ2], by simp [τ2, τ1]⟩
  have r4 : Run B (minTo "r" "x" "n") τ3 (τ3.setVar "r" (rB x)) 6 := by
    have e : rB x = min (min (2 ^ min (mB x) (nB x)) (nB x + 1)) (nB x) := by unfold rB; omega
    rw [e]
    exact run_minTo hx3 hn3 (by have := min_le_right (2 ^ min (mB x) (nB x)) (nB x + 1); omega) (by omega)
  set τ4 := τ3.setVar "r" (rB x)
  have hr := rB_le x
  have r5 : Run B (.assign "K" (.add (.mul (.lit 2) (V "r")) (.lit 3))) τ4 (τ4.setVar "K" (KB x)) 6 :=
    (Run.assign (ev_add (ev_mul (ev_lit (by omega)) (ev_var (by simp [τ4]) (by omega)) (by omega))
      (ev_lit (by omega)) (by omega))).mono (by simp)
  refine ⟨_, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq r5))))).mono (by simp; omega),
    (f3.setVar (by simp) _).setVar (by simp) _, by simp [τ4], by simp⟩

/-- The flag of a real job. -/
def bitR (x : List ℕ) (j : ℕ) : ℕ := if realB x j then 1 else 0
/-- The flag of a head. -/
def bitH (x : List ℕ) (j : ℕ) : ℕ := if headB x j then 1 else 0

theorem bitR_le (x : List ℕ) (j : ℕ) : bitR x j ≤ 1 := by unfold bitR; split_ifs <;> omega
theorem bitH_le (x : List ℕ) (j : ℕ) : bitH x j ≤ 1 := by unfold bitH; split_ifs <;> omega

/-- **The flags of one job.** -/
theorem run_flag (bd : BB x B) {τ : Env} (h : BC x τ) {k0 : ℕ} (hk0 : k0 < nB x) (hj : τ.vars "j" = k0)
    (hrl : τ.arrs "rl" = upto x.length k0 (bitR x)) (hhf : τ.arrs "hf" = upto x.length k0 (bitH x)) :
    ∃ τ', Run B flagBody τ τ' ((60 * x.length + 414) * x.length + 70) ∧ BC x τ' ∧
      τ'.vars "j" = k0 + 1 ∧ τ'.arrs "rl" = upto x.length (k0 + 1) (bitR x) ∧
      τ'.arrs "hf" = upto x.length (k0 + 1) (bitH x) ∧ τ'.out = τ.out := by
  have hnL := nB_le x
  have hidx := bd.idx
  have r1 := ev_rd h.a h.L (e := .add (.lit 3) (V "j")) (ev_add (ev_lit (by omega)) (ev_var hj (by omega))
    (by omega)) bd.M bd.Lt "p"
  rw [show x.getD (3 + k0) 0 = pB x k0 from rfl] at r1
  set τ1 := τ.setVar "p" (pB x k0)
  have h1 : BC x τ1 := h.setVar (by decide) _
  have r2 := ev_rd h1.a h1.L (e := .add (.add (.lit 3) (V "n")) (V "j"))
    (ev_add (ev_add (ev_lit (by omega)) (ev_var h1.n (by omega)) (by omega)) (ev_var (v := k0) (by simp [τ1, hj])
      (by omega)) (by omega)) bd.M bd.Lt "d"
  rw [show x.getD (3 + nB x + k0) 0 = dB x k0 from rfl] at r2
  set τ2 := τ1.setVar "d" (dB x k0)
  set τ3 := τ2.setVar "z" 0
  have r3 : Run B (.assign "z" (.lit 0)) τ2 τ3 2 := Run.assign (ev_lit (by omega))
  have hp3 : τ3.vars "p" = pB x k0 := by simp [τ3, τ2, τ1]
  have hd3 : τ3.vars "d" = dB x k0 := by simp [τ3, τ2]
  have hpB := bd.g (3 + k0)
  have hdB := bd.g (3 + nB x + k0)
  have hdM : dB x k0 ≤ mx x := getD_le_max x _
  have r4 : Run B (.ite (.lt (.lit 0) (V "p")) (.ite (.lt (V "p") (.add (V "d") (.lit 1))) (.assign "z" (.lit 1))
      .skip) .skip) τ3 (τ3.setVar "z" (bitR x k0)) 12 := by
    have c1 : (Cond.lt (.lit 0) (V "p")).evalB B τ3 = some (decide (0 < pB x k0)) :=
      evalB_condLt (ev_lit (by omega)) (ev_var hp3 hpB)
    have c2 : (Cond.lt (V "p") (.add (V "d") (.lit 1))).evalB B τ3 = some (decide (pB x k0 < dB x k0 + 1)) :=
      evalB_condLt (ev_var hp3 hpB) (ev_add (ev_var hd3 hdB) (ev_lit (by omega)) (by omega))
    by_cases hp0 : 0 < pB x k0
    · by_cases hpd : pB x k0 < dB x k0 + 1
      · have e : bitR x k0 = 1 := by simp [bitR, realB, hp0, show pB x k0 ≤ dB x k0 by omega]
        rw [e]
        exact (Run.ite_true (by rw [c1]; simp [hp0]) (Run.ite_true (by rw [c2]; simp [hpd])
          (Run.assign (ev_lit (by omega))))).mono (by simp)
      · have e : bitR x k0 = 0 := by simp [bitR, realB, show ¬ pB x k0 ≤ dB x k0 by omega]
        rw [e]
        have : τ3.setVar "z" 0 = τ3 := by
          simp only [τ3, Env.setVar]; congr 1; funext y; split_ifs <;> simp_all
        rw [this]
        exact (Run.ite_true (by rw [c1]; simp [hp0]) (Run.ite_false (by rw [c2]; simp [hpd]) Run.skip)).mono
          (by simp)
    · have e : bitR x k0 = 0 := by simp [bitR, realB, show pB x k0 = 0 by omega]
      rw [e]
      have : τ3.setVar "z" 0 = τ3 := by
        simp only [τ3, Env.setVar]; congr 1; funext y; split_ifs <;> simp_all
      rw [this]
      exact (Run.ite_false (by rw [c1]; simp [hp0]) Run.skip).mono (by simp)
  set τ4 := τ3.setVar "z" (bitR x k0)
  have r5 : Run B (.store "rl" (V "j") (V "z")) τ4 (τ4.setArr "rl" k0 (bitR x k0)) 3 :=
    Run.store (ev_var (by simp [τ4, τ3, τ2, τ1, hj]) (by omega)) (ev_var (by simp [τ4])
      (by have := bitR_le x k0; omega)) (by simp [τ4, τ3, τ2, τ1, hrl]; omega)
  set τ5 := τ4.setArr "rl" k0 (bitR x k0)
  set τ6 := τ5.setVar "f" 1
  have r6 : Run B (.assign "f" (.lit 1)) τ5 τ6 2 := Run.assign (ev_lit (by omega))
  have h6 : BC x τ6 := ((((((h.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
    (by decide) _).setArr (by decide) _ _).setVar (by decide) _)
  -- the earlier points of the kind
  obtain ⟨τ7, r7, -, h7, hj7, hp7, hf7, ha7, ho7⟩ := run_forLoop (B := B) "k" "j"
    (.seq sameCom (.seq (.ite (.eq (V "e") (.lit 1)) (.assign "f" (.lit 0)) .skip) (incr "k"))) k0
    (60 * x.length + 414) (by omega)
    (fun i σ => σ.vars "k" = i ∧ BC x σ ∧ σ.vars "j" = k0 ∧ σ.vars "p" = pB x k0 ∧
      σ.vars "f" = (if (List.range i).any (fun k => sameB x k0 k) then 0 else 1) ∧
      σ.arrs = τ6.arrs ∧ σ.out = τ6.out)
    (fun i σ h => h.1) (fun i σ h => h.2.2.1)
    (fun i hi σ ⟨hk, hb, hjv, hpv, hfv, hav, hov⟩ => by
      obtain ⟨σ1, q1, g1, he1⟩ := run_same bd hb hjv hk hk0 (by omega)
      have hb1 : BC x σ1 := hb.ofFr g1 (by decide)
      have hany : (List.range (i + 1)).any (fun k => sameB x k0 k) =
          ((List.range i).any (fun k => sameB x k0 k) || sameB x k0 i) := by
        rw [List.range_succ, List.any_append]; simp
      have hc : (Cond.eq (V "e") (.lit 1)).evalB B σ1 = some ((if sameB x k0 i then 1 else 0) == 1) :=
        evalB_condEq (ev_var he1 (by split_ifs <;> omega)) (ev_lit (by omega))
      have hk1 : σ1.vars "k" = i := by rw [g1.2.2 "k" (by decide), hk]
      by_cases hs : sameB x k0 i = true
      · refine ⟨_, (q1.seq ((Run.ite_true (by rw [hc]; simp [hs]) (Run.assign (ev_lit (n := 0) (by omega)))).seq
          (run_incr "k" (k := i) (by simp [hk1]) (by omega)))).mono (by simp), by simp,
          (hb1.setVar (by decide) _).setVar (by decide) _, by simp [g1.2.2 "j" (by decide), hjv],
          by simp [g1.2.2 "p" (by decide), hpv], by simp [hany, hs], by simp [g1.1, hav],
          by simp [g1.2.1, hov]⟩
      · refine ⟨_, (q1.seq ((Run.ite_false (by rw [hc]; simp [hs]) Run.skip).seq
          (run_incr "k" (k := i) hk1 (by omega)))).mono (by simp), by simp,
          hb1.setVar (by decide) _, by simp [g1.2.2 "j" (by decide), hjv],
          by simp [g1.2.2 "p" (by decide), hpv], by simp [hany, hs, g1.2.2 "f" (by decide), hfv],
          by simp [g1.1, hav], by simp [g1.2.1, hov]⟩)
    (σ := τ6) ⟨by simp, h6.setVar (by decide) _, by simp [τ6, τ5, τ4, τ3, τ2, τ1, hj],
      by simp [τ6, τ5, τ4, τ3, τ2, τ1], by simp [τ6], by simp, by simp⟩
  have c8 : (Cond.eq (V "p") (.lit 0)).evalB B τ7 = some (pB x k0 == 0) :=
    evalB_condEq (ev_var hp7 hpB) (ev_lit (by omega))
  have r8 : Run B (.ite (.eq (V "p") (.lit 0)) .skip (.assign "f" (.lit 0))) τ7 (τ7.setVar "f" (bitH x k0)) 6 := by
    by_cases hp0 : pB x k0 = 0
    · have e : bitH x k0 = (if (List.range k0).any (fun k => sameB x k0 k) then 0 else 1) := by
        unfold bitH headB; rw [hp0]; split_ifs <;> simp_all
      have : τ7.setVar "f" (bitH x k0) = τ7 := by
        rw [e, ← hf7]; simp only [Env.setVar]; congr 1; funext y; split_ifs <;> simp_all
      rw [this]
      exact (Run.ite_true (by rw [c8]; simp [hp0]) Run.skip).mono (by simp)
    · have e : bitH x k0 = 0 := by simp [bitH, headB, hp0]
      rw [e]
      exact (Run.ite_false (by rw [c8]; simp [hp0]) (Run.assign (ev_lit (by omega)))).mono (by simp)
  set τ8 := τ7.setVar "f" (bitH x k0)
  have r9 : Run B (.store "hf" (V "j") (V "f")) τ8 (τ8.setArr "hf" k0 (bitH x k0)) 3 :=
    Run.store (ev_var (by simp [τ8, hj7]) (by omega)) (ev_var (by simp [τ8])
      (by have := bitH_le x k0; omega)) (by simp [τ8, ha7, τ6, τ5, τ4, τ3, τ2, τ1, hhf]; omega)
  set τ9 := τ8.setArr "hf" k0 (bitH x k0)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    (run_incr "j" (k := k0) (by simp [τ9, τ8, hj7]) (by omega))))))))))).mono ?_,
    ((h7.setVar (by decide) _).setArr (by decide) _ _).setVar (by decide) _, by simp, ?_, ?_, ?_⟩
  · have : (60 * x.length + 414 + 4) * k0 ≤ (60 * x.length + 414 + 4) * x.length :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [Expr.size]
    nlinarith
  · simp [τ9, τ8, ha7, τ6, τ5, τ4, τ3, τ2, τ1, hrl]
    exact store_upto (by omega)
  · simp [τ9, τ8, ha7, τ6, τ5, τ4, τ3, τ2, τ1, hhf]
    exact store_upto (by omega)
  · simp [τ9, τ8, ho7, τ6, τ5, τ4, τ3, τ2, τ1]

end BW

end Lax434175Proofs.P200Programs
