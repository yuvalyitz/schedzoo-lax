import Mathlib.Tactic
import Lax434175Proofs.HighMultiplicityMap
import Lax434175Proofs.IsemPrograms
import Lax434175Proofs.P200ProgramsParse
import Lax434175Proofs.Cost.Polytime

/-!
The word map `hmWord` of `HighMultiplicityMap` as an IMP+ program of lax-808846, polynomial on
every word.

The program reads the word into an array, finds where the record of every job begins and how
long it is, and then, for every job `j`, compares its tuple with the tuple of every job `i`,
entry by entry (a scan over both tuples): it counts the jobs with the same tuple and notes
whether `j` is the first of them. A second pass computes the rank of every first job: the
number of first jobs whose tuple, its number in front, is smaller. Then it writes the header,
the number of distinct tuples, for every rank `r` the tuple of the first job of rank `r`, the
two blocks and the threshold. With `n` jobs and a word of length `|u|` it makes `O(n²)`
comparisons of `O(|u|)` steps each, `O(|u|³)` in all.
-/

namespace Lax434175Proofs.HighMultiplicityProgram
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost
open Lax434175Proofs.IsemPrograms (V incr prelude arrW run_prelude getD_le_max ev_rd minTo run_minTo
  bndCW upto store_upto upto_get upto_zero filter_range_succ)
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub ind ev_ind indN indN_le)
open Lax434175Proofs.P200Programs (nA posA nA_le posA_le' posA_succ run_incr)
open Lax434175Proofs.HighMultiplicityMap

/-- The largest entry. -/
local notation "mx" => Lax434175.Results.maxEntry

/-! ### The program -/

/-- `1` when the values are equal, `0` otherwise. -/
def eqE (e f : Expr) : Expr := .sub (.lit 1) (.add (.sub e f) (.sub f e))

/-- `ps[j] := q`; `ln[j] := min(a[q], L)`; `q := q + 1 + a[q]`. -/
def posBody : Com :=
  .seq (.store "ps" (V "j") (V "q")) <|
  .seq (rdG "a" "L" "v" (V "q")) <|
  .seq (minTo "c" "v" "L") <|
  .seq (.store "ln" (V "j") (V "c")) <|
  .seq (.assign "q" (.add (.add (V "q") (.lit 1)) (V "v"))) <|
  incr "j"

/-- Where the tuple of job `t` is: its record from `P` on, `N` long, its three numbers from `O`
on, `T` entries in all. -/
def setupT (t P N O T : String) : Com :=
  .seq (.assign P (.add (.get "ps" (V t)) (.lit 1))) <|
  .seq (.assign N (.get "ln" (V t))) <|
  .seq (.assign O (.add (V "o") (.mul (.lit 3) (V t)))) <|
  .assign T (.add (V N) (.lit 3))

/-- Read entry `k` of the tuple into `dst`. -/
def readT (P N O dst : String) : Com :=
  .seq (.assign "h" (ind (.sub (V N) (V "k")))) <|
  .seq (.assign "x" (.add (.mul (V "h") (.add (V P) (V "k")))
    (.mul (.sub (.lit 1) (V "h")) (.sub (.add (V O) (V "k")) (V N))))) <|
  rdG "a" "L" dst (V "x")

/-- One position of the scan of two tuples. -/
def cmpStep : Com :=
  .seq (.assign "f" (ind (.sub (V "T1") (V "k")))) <|
  .seq (.assign "g" (ind (.sub (V "T2") (V "k")))) <|
  .seq (readT "P1" "N1" "O1" "va") <|
  .seq (readT "P2" "N2" "O2" "vb") <|
  .seq (.assign "w" (.add (.add (.mul (.mul (V "f") (V "g"))
      (.add (ind (.sub (V "vb") (V "va"))) (.mul (.lit 2) (ind (.sub (V "va") (V "vb"))))))
    (.mul (.mul (V "f") (.sub (.lit 1) (V "g"))) (.lit 2))) (.mul (.sub (.lit 1) (V "f")) (V "g")))) <|
  .seq (.assign "st" (.add (V "st") (.mul (.sub (.lit 1) (ind (V "st"))) (V "w")))) <|
  incr "k"

/-- `st := ` the comparison of the tuples of jobs `i` and `j`. -/
def cmpCom : Com :=
  .seq (setupT "i" "P1" "N1" "O1" "T1") <|
  .seq (setupT "j" "P2" "N2" "O2" "T2") <|
  .seq (.assign "st" (.lit 0)) <|
  .seq (.assign "K" (.add (V "T1") (V "T2"))) <|
  forLoop "k" "K" cmpStep

/-- Count job `i` if it has the tuple of job `j`; `j` is not first if `i < j` does. -/
def cntInner : Com :=
  .seq cmpCom <|
  .seq (.assign "e" (.sub (.lit 1) (V "st"))) <|
  .seq (.assign "c" (.add (V "c") (V "e"))) <|
  .seq (.assign "fl" (.mul (V "fl") (.sub (.lit 1) (.mul (V "e") (ind (.sub (V "j") (V "i"))))))) <|
  incr "i"

/-- `cn[j]` and `fs[j]`, and `d` counts the first jobs. -/
def cntBody : Com :=
  .seq (.assign "c" (.lit 0)) <| .seq (.assign "fl" (.lit 1)) <|
  .seq (forLoop "i" "n" cntInner) <|
  .seq (.store "cn" (V "j") (V "c")) <| .seq (.store "fs" (V "j") (V "fl")) <|
  .seq (.assign "d" (.add (V "d") (V "fl"))) <|
  incr "j"

/-- Count job `i` if it is first with a smaller tuple than job `j`. -/
def rkInner : Com :=
  .seq cmpCom <|
  .seq (.assign "ci" (.get "cn" (V "i"))) <| .seq (.assign "cj" (.get "cn" (V "j"))) <|
  .seq (.assign "r" (.add (V "r") (.mul (.get "fs" (V "i"))
    (.add (ind (.sub (V "cj") (V "ci"))) (.mul (eqE (V "ci") (V "cj")) (eqE (V "st") (.lit 1))))))) <|
  incr "i"

/-- `rk[j]`. -/
def rkBody : Com :=
  .seq (.assign "r" (.lit 0)) <| .seq (forLoop "i" "n" rkInner) <|
  .seq (.store "rk" (V "j") (V "r")) <| incr "j"

/-- Write entry `k` of the tuple. -/
def wtStep : Com := .seq (readT "P1" "N1" "O1" "va") <| .seq (.write (V "va")) <| incr "k"

/-- Write the tuple of job `j` with its number and its length in front. -/
def writeTup : Com :=
  .seq (setupT "j" "P1" "N1" "O1" "T1") <|
  .seq (.write (.add (V "N1") (.lit 4))) <| .seq (.write (.get "cn" (V "j"))) <|
  forLoop "k" "T1" wtStep

/-- Write the tuple of job `j` if it is first with rank `r`. -/
def outInner : Com :=
  .seq (.ite (.eq (.mul (.get "fs" (V "j")) (.add (.get "rk" (V "j")) (.lit 1))) (.add (V "r") (.lit 1)))
    writeTup .skip) <|
  incr "j"

/-- Write the tuple of rank `r`. -/
def outBody : Com := .seq (forLoop "j" "n" outInner) (incr "r")

/-- Copy the number at `q + k`. -/
def midBody : Com := .seq (rdG "a" "L" "v" (.add (V "q") (V "k"))) <| .seq (.write (V "v")) <| incr "k"

/-- The whole program. -/
def com : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 1)) <| .seq (minTo "n" "c" "L") <|
  .seq (.assign "q" (.lit 3)) <|
  .seq (forLoop "j" "n" posBody) <|
  .seq (.assign "o" (.sub (.sub (V "L") (.lit 2)) (.mul (.lit 3) (V "n")))) <|
  .seq (.assign "d" (.lit 0)) <|
  .seq (forLoop "j" "n" cntBody) <|
  .seq (forLoop "j" "n" rkBody) <|
  .seq (.write (.lit 1)) <|
  .seq (rdG "a" "L" "v" (.lit 1)) <| .seq (.write (V "v")) <|
  .seq (rdG "a" "L" "v" (.lit 2)) <| .seq (.write (V "v")) <|
  .seq (.write (V "d")) <|
  .seq (forLoop "r" "n" outBody) <|
  .seq (.assign "z" (.sub (V "o") (V "q"))) <|
  .seq (forLoop "k" "z" midBody) <|
  .seq (rdG "a" "L" "v" (.sub (V "L") (.lit 2))) <| .seq (.write (V "v")) <|
  .seq (rdG "a" "L" "v" (.sub (V "L") (.lit 1))) <| .write (V "v")

/-- The scalars, the arrays, and the temporaries. -/
def layout : Layout :=
  ⟨["L", "i", "v", "c", "n", "q", "j", "o", "d", "P1", "N1", "O1", "T1", "P2", "N2", "O2", "T2",
    "st", "K", "k", "f", "g", "h", "x", "va", "vb", "w", "e", "fl", "ci", "cj", "r", "z"],
    ["a", "ps", "ln", "cn", "fs", "rk"], 12⟩

theorem com_ok : Com.Ok layout com := by
  simp [com, posBody, setupT, readT, cmpStep, cmpCom, cntInner, cntBody, rkInner, rkBody, wtStep,
    writeTup, outInner, outBody, midBody, eqE, prelude, minTo, rdG, ind,
    Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### Running the program -/

/-- What the value bound must admit. -/
structure Bd (u : List ℕ) (B : ℕ) : Prop where
  pos : 3 + u.length * (mx u + 1) + 2 * mx u + 20 * u.length + 100 < B

theorem bd_of {u : List ℕ} {B : ℕ} (hB : 8 * (u.length + mx u + 8) ^ 2 ≤ B) : Bd u B :=
  ⟨by nlinarith⟩

/-- The names the phases after the positions keep fixed. -/
def ctxNames : List String := ["L", "n", "q", "o"]

/-- The arrays the phases after the positions keep fixed. -/
def ctxArrs : List String := ["a", "ps", "ln"]

/-- What stays fixed once the records are located. -/
structure Ctx (u : List ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = arrW u
  L : τ.vars "L" = u.length
  n : τ.vars "n" = nA u
  q : τ.vars "q" = posA u (nA u)
  o : τ.vars "o" = obH u
  ps : τ.arrs "ps" = upto u.length (nA u) (posA u)
  ln : τ.arrs "ln" = upto u.length (nA u) (lnH u)

section Runs
variable {B : ℕ} {u : List ℕ}

theorem Ctx.of {τ τ' : Env} (h : Ctx u τ) (hv : ∀ y ∈ ctxNames, τ'.vars y = τ.vars y)
    (ha : ∀ b ∈ ctxArrs, τ'.arrs b = τ.arrs b) : Ctx u τ' :=
  ⟨by rw [ha "a" (by decide), h.a], by rw [hv "L" (by decide), h.L], by rw [hv "n" (by decide), h.n],
    by rw [hv "q" (by decide), h.q], by rw [hv "o" (by decide), h.o],
    by rw [ha "ps" (by decide), h.ps], by rw [ha "ln" (by decide), h.ln]⟩

/-- A command that touches none of the fixed names keeps the context. -/
theorem Ctx.run {τ τ' : Env} {c : Com} {K : ℕ} (h : Ctx u τ) (hr : Run B c τ τ' K)
    (hv : ∀ y ∈ ctxNames, y ∉ c.wvars) (ha : ∀ b ∈ ctxArrs, b ∉ c.warrs) : Ctx u τ' :=
  h.of (fun y hy => hr.frame_var y (hv y hy)) (fun b hb => hr.frame_arr b (ha b hb))

theorem Ctx.setVar {τ : Env} (h : Ctx u τ) {y : String} (hy : y ∉ ctxNames) (w : ℕ) :
    Ctx u (τ.setVar y w) :=
  h.of (fun z hz => by simp [ne_of_mem_of_not_mem hz hy]) (fun b _ => by simp)

theorem Ctx.setArr {τ : Env} (h : Ctx u τ) {b : String} (hb : b ∉ ctxArrs) (i w : ℕ) :
    Ctx u (τ.setArr b i w) :=
  h.of (fun z _ => by simp) (fun c hc => by simp [ne_of_mem_of_not_mem hc hb])

theorem Ctx.out {τ : Env} (h : Ctx u τ) (o : List ℕ) : Ctx u { τ with out := o } :=
  ⟨h.a, h.L, h.n, h.q, h.o, h.ps, h.ln⟩

theorem mul_le_of_le_one {a : ℕ} (h : a ≤ 1) (b : ℕ) : a * b ≤ b := by
  interval_cases a <;> simp

theorem obH_le (u : List ℕ) : obH u ≤ u.length := by unfold obH; omega

theorem lnH_le (u : List ℕ) (j : ℕ) : lnH u j ≤ u.length := min_le_right _ _

theorem Bd.M (bd : Bd u B) : mx u < B := by have := bd.pos; omega

theorem Bd.Lt (bd : Bd u B) : u.length < B := by have := bd.pos; omega

theorem Bd.posA (bd : Bd u B) {j : ℕ} (hj : j ≤ nA u) (c : ℕ) (hc : c ≤ 2 * mx u + 20 * u.length + 100) :
    posA u j + c < B := by
  have := posA_le' hj; have := bd.pos; omega

theorem Ctx.ps_get {τ : Env} (h : Ctx u τ) {j : ℕ} (hj : j < nA u) :
    (τ.arrs "ps")[j]? = some (posA u j) := by
  rw [h.ps]; exact upto_get hj (by have := nA_le u; omega)

theorem Ctx.ln_get {τ : Env} (h : Ctx u τ) {j : ℕ} (hj : j < nA u) :
    (τ.arrs "ln")[j]? = some (lnH u j) := by
  rw [h.ln]; exact upto_get hj (by have := nA_le u; omega)

/-- **Where the tuple of job `j` is.** -/
theorem run_setupT (bd : Bd u B) {τ : Env} (h : Ctx u τ) {t P N O T : String} {j : ℕ}
    (hj : j < nA u) (ht : τ.vars t = j) (h1 : P ≠ t) (h2 : N ≠ t) (h3 : P ≠ "o") (h4 : N ≠ "o")
    (h5 : O ≠ N) :
    Run B (setupT t P N O T) τ ((((τ.setVar P (posA u j + 1)).setVar N (lnH u j)).setVar O
      (obH u + 3 * j)).setVar T (lnH u j + 3)) 18 := by
  have hn := nA_le u
  have hL := lnH_le u j
  have hob := obH_le u
  have hP := bd.posA hj.le 1 (by omega)
  have hb := bd.pos
  have r1 : Run B (.assign P (.add (.get "ps" (V t)) (.lit 1))) τ (τ.setVar P (posA u j + 1)) 5 :=
    (Run.assign (ev_add (evalB_get (ev_var ht (by omega)) (h.ps_get hj) (by omega)) (ev_lit (by omega))
      (by omega))).mono (by simp)
  set τ1 := τ.setVar P (posA u j + 1)
  have r2 : Run B (.assign N (.get "ln" (V t))) τ1 (τ1.setVar N (lnH u j)) 3 :=
    (Run.assign (evalB_get (ev_var (v := j) (by simp [τ1, h1.symm, ht]) (by omega))
      (by simpa [τ1] using h.ln_get hj) (by omega))).mono (by simp)
  set τ2 := τ1.setVar N (lnH u j)
  have r3 : Run B (.assign O (.add (V "o") (.mul (.lit 3) (V t)))) τ2 (τ2.setVar O (obH u + 3 * j)) 6 :=
    (Run.assign (ev_add (ev_var (by simp [τ2, τ1, h4.symm, h3.symm, h.o]) (by omega))
      (ev_mul (ev_lit (by omega)) (ev_var (by simp [τ2, τ1, h2.symm, h1.symm, ht]) (by omega))
        (by omega)) (by omega))).mono (by simp)
  set τ3 := τ2.setVar O (obH u + 3 * j)
  have r4 : Run B (.assign T (.add (V N) (.lit 3))) τ3 (τ3.setVar T (lnH u j + 3)) 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ3, τ2, h5.symm]) (by omega)) (ev_lit (by omega))
      (by omega))).mono (by simp)
  exact (r1.seq (r2.seq (r3.seq r4))).mono (by norm_num)

/-- **Reading entry `k` of the tuple of job `j`.** -/
theorem run_readT (bd : Bd u B) {τ : Env} (h : Ctx u τ) {P N O dst : String} {j k : ℕ}
    (hj : j < nA u) (hk : k ≤ 2 * u.length + 6) (hP : τ.vars P = posA u j + 1)
    (hN : τ.vars N = lnH u j) (hO : τ.vars O = obH u + 3 * j) (hkv : τ.vars "k" = k)
    (n1 : P ≠ "h") (n2 : N ≠ "h") (n3 : O ≠ "h") :
    Run B (readT P N O dst) τ (((τ.setVar "h" (indN (lnH u j - k))).setVar "x" (idxH u j k)).setVar
      dst (u.getD (idxH u j k) 0)) 36 := by
  have hn := nA_le u
  have hL := lnH_le u j
  have hob := obH_le u
  have hP' := bd.posA hj.le (1 + k) (by omega)
  have hb := bd.pos
  have r1 : Run B (.assign "h" (ind (.sub (V N) (V "k")))) τ (τ.setVar "h" (indN (lnH u j - k))) 8 :=
    (Run.assign (ev_ind (ev_sub (ev_var hN (by omega)) (ev_var hkv (by omega))) (by omega))).mono
      (by simp)
  set τ1 := τ.setVar "h" (indN (lnH u j - k))
  have hh := indN_le (lnH u j - k)
  have e1 : τ1.vars "h" = indN (lnH u j - k) := by simp [τ1]
  have e2 : τ1.vars P = posA u j + 1 := by simp [τ1, n1, hP]
  have e3 : τ1.vars N = lnH u j := by simp [τ1, n2, hN]
  have e4 : τ1.vars O = obH u + 3 * j := by simp [τ1, n3, hO]
  have e5 : τ1.vars "k" = k := by simp [τ1, hkv]
  have hx : indN (lnH u j - k) * (posA u j + 1 + k) +
      (1 - indN (lnH u j - k)) * (obH u + 3 * j + k - lnH u j) = idxH u j k := by
    rw [idx_eq]; unfold idxH; split_ifs <;> omega
  have hm1 : indN (lnH u j - k) * (posA u j + 1 + k) ≤ posA u j + 1 + k :=
    mul_le_of_le_one hh _
  have hm2 : (1 - indN (lnH u j - k)) * (obH u + 3 * j + k - lnH u j) ≤ obH u + 3 * j + k :=
    (mul_le_of_le_one (by omega) _).trans (Nat.sub_le _ _)
  have hidx : idxH u j k < B := by
    unfold idxH; split_ifs <;> omega
  have r2 : Run B (.assign "x" (.add (.mul (V "h") (.add (V P) (V "k")))
      (.mul (.sub (.lit 1) (V "h")) (.sub (.add (V O) (V "k")) (V N))))) τ1 (τ1.setVar "x" (idxH u j k))
      16 := by
    refine (Run.assign ?_).mono (by simp)
    rw [← hx]
    exact ev_add (ev_mul (ev_var e1 (by omega)) (ev_add (ev_var e2 (by omega)) (ev_var e5 (by omega))
      (by omega)) (by omega)) (ev_mul (ev_sub (ev_lit (by omega)) (ev_var e1 (by omega)))
      (ev_sub (ev_add (ev_var e4 (by omega)) (ev_var e5 (by omega)) (by omega)) (ev_var e3 (by omega)))
      (by omega)) (by omega)
  set τ2 := τ1.setVar "x" (idxH u j k)
  have hc2 : Ctx u τ2 := (h.setVar (by decide) _).setVar (by decide) _
  have r3 := ev_rd (B := B) hc2.a hc2.L (e := V "x") (ev_var (by simp [τ2]) hidx) bd.M bd.Lt dst
  exact (r1.seq (r2.seq r3)).mono (by simp)

theorem cmpUp_le (l l' : List ℕ) : ∀ k, cmpUp l l' k ≤ 2
  | 0 => by simp [cmpUp]
  | k + 1 => by
    rw [cmpUp]; split_ifs
    · unfold locC; split_ifs <;> omega
    · exact cmpUp_le l l' k

/-- The cost of one position of the scan. -/
def stepCost : ℕ := 140

/-- **One position of the scan.** -/
theorem run_cmpStep (bd : Bd u B) {σ : Env} (h : Ctx u σ) {i j k s : ℕ} (hi : i < nA u)
    (hj : j < nA u) (hk : k < lnH u i + 3 + (lnH u j + 3))
    (hP1 : σ.vars "P1" = posA u i + 1) (hN1 : σ.vars "N1" = lnH u i) (hO1 : σ.vars "O1" = obH u + 3 * i)
    (hT1 : σ.vars "T1" = lnH u i + 3)
    (hP2 : σ.vars "P2" = posA u j + 1) (hN2 : σ.vars "N2" = lnH u j) (hO2 : σ.vars "O2" = obH u + 3 * j)
    (hT2 : σ.vars "T2" = lnH u j + 3) (hkv : σ.vars "k" = k) (hs : σ.vars "st" = s) (hs2 : s ≤ 2) :
    ∃ σ', Run B cmpStep σ σ' stepCost ∧
      σ'.vars "st" = (if s = 0 then locC (tupH u i) (tupH u j) k else s) ∧ σ'.vars "k" = k + 1 := by
  have hn := nA_le u
  have hLi := lnH_le u i
  have hLj := lnH_le u j
  have hb := bd.pos
  set f := indN (lnH u i + 3 - k)
  set g := indN (lnH u j + 3 - k)
  have hf : f ≤ 1 := indN_le _
  have hg : g ≤ 1 := indN_le _
  have r1 : Run B (.assign "f" (ind (.sub (V "T1") (V "k")))) σ (σ.setVar "f" f) 8 :=
    (Run.assign (ev_ind (ev_sub (ev_var hT1 (by omega)) (ev_var hkv (by omega))) (by omega))).mono
      (by simp)
  set σ1 := σ.setVar "f" f
  have r2 : Run B (.assign "g" (ind (.sub (V "T2") (V "k")))) σ1 (σ1.setVar "g" g) 8 :=
    (Run.assign (ev_ind (ev_sub (ev_var (by simp [σ1, hT2]) (by omega))
      (ev_var (by simp [σ1, hkv]) (by omega))) (by omega))).mono (by simp)
  set σ2 := σ1.setVar "g" g
  have hc2 : Ctx u σ2 := (h.setVar (by decide) _).setVar (by decide) _
  have r3 := run_readT bd hc2 (P := "P1") (N := "N1") (O := "O1") (dst := "va") hi (k := k) (by omega)
    (by simp [σ2, σ1, hP1]) (by simp [σ2, σ1, hN1]) (by simp [σ2, σ1, hO1]) (by simp [σ2, σ1, hkv])
    (by decide) (by decide) (by decide)
  set va := u.getD (idxH u i k) 0
  set σ3 := ((σ2.setVar "h" (indN (lnH u i - k))).setVar "x" (idxH u i k)).setVar "va" va
  have hc3 : Ctx u σ3 := ((hc2.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
  have r4 := run_readT bd hc3 (P := "P2") (N := "N2") (O := "O2") (dst := "vb") hj (k := k) (by omega)
    (by simp [σ3, σ2, σ1, hP2]) (by simp [σ3, σ2, σ1, hN2]) (by simp [σ3, σ2, σ1, hO2])
    (by simp [σ3, σ2, σ1, hkv]) (by decide) (by decide) (by decide)
  set vb := u.getD (idxH u j k) 0
  set σ4 := ((σ3.setVar "h" (indN (lnH u j - k))).setVar "x" (idxH u j k)).setVar "vb" vb
  have hva : va ≤ mx u := getD_le_max u _
  have hvb : vb ≤ mx u := getD_le_max u _
  have e1 : σ4.vars "f" = f := by simp [σ4, σ3, σ2, σ1]
  have e2 : σ4.vars "g" = g := by simp [σ4, σ3, σ2, σ1]
  have e3 : σ4.vars "va" = va := by simp [σ4, σ3]
  have e4 : σ4.vars "vb" = vb := by simp [σ4]
  have i1 := indN_le (vb - va)
  have i2 := indN_le (va - vb)
  have m1 : f * g ≤ 1 := (mul_le_of_le_one hf g).trans hg
  have m2 : f * g * (indN (vb - va) + 2 * indN (va - vb)) ≤ 3 :=
    (mul_le_of_le_one m1 _).trans (by omega)
  have m3 : f * (1 - g) ≤ 1 := (mul_le_of_le_one hf _).trans (by omega)
  have m4 : f * (1 - g) * 2 ≤ 2 := mul_le_of_le_one m3 _
  have m5 : (1 - f) * g ≤ 1 := (mul_le_of_le_one (by omega) g).trans hg
  have hw : locN f g va vb ≤ 6 := by unfold locN; omega
  have r5 : Run B (.assign "w" (.add (.add (.mul (.mul (V "f") (V "g"))
      (.add (ind (.sub (V "vb") (V "va"))) (.mul (.lit 2) (ind (.sub (V "va") (V "vb"))))))
      (.mul (.mul (V "f") (.sub (.lit 1) (V "g"))) (.lit 2))) (.mul (.sub (.lit 1) (V "f")) (V "g"))))
      σ4 (σ4.setVar "w" (locN f g va vb)) 36 :=
    (Run.assign (ev_add (ev_add (ev_mul (ev_mul (ev_var e1 (by omega)) (ev_var e2 (by omega)) (by omega))
      (ev_add (ev_ind (ev_sub (ev_var e4 (by omega)) (ev_var e3 (by omega))) (by omega))
        (ev_mul (ev_lit (by omega)) (ev_ind (ev_sub (ev_var e3 (by omega)) (ev_var e4 (by omega)))
          (by omega)) (by omega)) (by omega)) (by omega))
      (ev_mul (ev_mul (ev_var e1 (by omega)) (ev_sub (ev_lit (by omega)) (ev_var e2 (by omega)))
        (by omega)) (ev_lit (by omega)) (by omega)) (by omega))
      (ev_mul (ev_sub (ev_lit (by omega)) (ev_var e1 (by omega))) (ev_var e2 (by omega)) (by omega))
      (by unfold locN at hw; omega))).mono (by simp)
  set σ5 := σ4.setVar "w" (locN f g va vb)
  have hst : (1 - indN s) * locN f g va vb ≤ 6 := (mul_le_of_le_one (by omega) _).trans hw
  have r6 : Run B (.assign "st" (.add (V "st") (.mul (.sub (.lit 1) (ind (V "st"))) (V "w")))) σ5
      (σ5.setVar "st" (s + (1 - indN s) * locN f g va vb)) 12 :=
    (Run.assign (ev_add (ev_var (by simp [σ5, σ4, σ3, σ2, σ1, hs]) (by omega))
      (ev_mul (ev_sub (ev_lit (by omega)) (ev_ind (ev_var (by simp [σ5, σ4, σ3, σ2, σ1, hs])
        (by omega)) (by omega))) (ev_var (by simp [σ5]) (by omega)) (by omega)) (by omega))).mono
      (by simp)
  set σ6 := σ5.setVar "st" (s + (1 - indN s) * locN f g va vb)
  have r7 := run_incr (B := B) (k := k) "k" (τ := σ6) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hkv])
    (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (by simp [stepCost]),
    ?_, by simp⟩
  have hloc : locN f g va vb = locC (tupH u i) (tupH u j) k := by
    have := locN_eq (tupH u i) (tupH u j) k (a := va) (b := vb)
      (fun hk => (tupH_getD u i hk).symm) (fun hk => (tupH_getD u j hk).symm)
    rwa [tupH_length, tupH_length] at this
  simp only [vars_setVar, if_neg (show ("st" : String) ≠ "k" by decide)]
  rw [show σ6.vars "st" = s + (1 - indN s) * locN f g va vb by simp [σ6], step_eq, hloc]

/-- The cost of a comparison. -/
def cmpCost (u : List ℕ) : ℕ := (stepCost + 4) * (2 * u.length + 6) + 48

/-- **The comparison of the tuples of jobs `i` and `j`.** -/
theorem run_cmp (bd : Bd u B) {τ : Env} (h : Ctx u τ) {i j : ℕ} (hi : i < nA u) (hj : j < nA u)
    (hiv : τ.vars "i" = i) (hjv : τ.vars "j" = j) :
    ∃ τ', Run B cmpCom τ τ' (cmpCost u) ∧ τ'.vars "st" = cmpL (tupH u i) (tupH u j) := by
  have hn := nA_le u
  have hLi := lnH_le u i
  have hLj := lnH_le u j
  have hb := bd.pos
  have r1 := run_setupT bd h (t := "i") (P := "P1") (N := "N1") (O := "O1") (T := "T1") hi hiv
    (by decide) (by decide) (by decide) (by decide) (by decide)
  set τ1 := (((τ.setVar "P1" (posA u i + 1)).setVar "N1" (lnH u i)).setVar "O1" (obH u + 3 * i)).setVar
    "T1" (lnH u i + 3)
  have hc1 : Ctx u τ1 :=
    (((h.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
  have r2 := run_setupT bd hc1 (t := "j") (P := "P2") (N := "N2") (O := "O2") (T := "T2") hj
    (by simp [τ1, hjv]) (by decide) (by decide) (by decide) (by decide) (by decide)
  set τ2 := (((τ1.setVar "P2" (posA u j + 1)).setVar "N2" (lnH u j)).setVar "O2" (obH u + 3 * j)).setVar
    "T2" (lnH u j + 3)
  have hc2 : Ctx u τ2 :=
    (((hc1.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
  have r3 : Run B (.assign "st" (.lit 0)) τ2 (τ2.setVar "st" 0) 2 := Run.assign (ev_lit (by omega))
  set N := lnH u i + 3 + (lnH u j + 3)
  have r4 : Run B (.assign "K" (.add (V "T1") (V "T2"))) (τ2.setVar "st" 0)
      ((τ2.setVar "st" 0).setVar "K" N) 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ2, τ1]) (by omega)) (ev_var (by simp [τ2]) (by omega))
      (by omega))).mono (by simp)
  set τ4 := (τ2.setVar "st" 0).setVar "K" N
  have hnw : ∀ y ∈ ["P1", "N1", "O1", "T1", "P2", "N2", "O2", "T2"], y ∉ cmpStep.wvars := by decide
  obtain ⟨τ5, r5, -, -, -, -, hst⟩ := run_forLoop (B := B) "k" "K" cmpStep N stepCost (by omega)
    (fun k σ => σ.vars "k" = k ∧ σ.vars "K" = N ∧ Ctx u σ ∧
      (∀ y ∈ ["P1", "N1", "O1", "T1", "P2", "N2", "O2", "T2"], σ.vars y = τ2.vars y) ∧
      σ.vars "st" = cmpUp (tupH u i) (tupH u j) k)
    (fun k σ h => h.1) (fun k σ h => h.2.1)
    (fun k hk σ ⟨hkv, hK, hc, hfr, hs⟩ => by
      obtain ⟨σ', r, hs', hk'⟩ := run_cmpStep bd hc hi hj hk
        (by rw [hfr "P1" (by decide)]; simp [τ2, τ1]) (by rw [hfr "N1" (by decide)]; simp [τ2, τ1])
        (by rw [hfr "O1" (by decide)]; simp [τ2, τ1]) (by rw [hfr "T1" (by decide)]; simp [τ2, τ1])
        (by rw [hfr "P2" (by decide)]; simp [τ2]) (by rw [hfr "N2" (by decide)]; simp [τ2])
        (by rw [hfr "O2" (by decide)]; simp [τ2]) (by rw [hfr "T2" (by decide)]; simp [τ2])
        hkv hs (cmpUp_le _ _ k)
      refine ⟨σ', r, hk', by rw [r.frame_var "K" (by decide), hK], hc.run r (by decide) (by decide),
        fun y hy => ?_, ?_⟩
      · rw [← hfr y hy]
        exact r.frame_var y (hnw y hy)
      · rw [hs']; rfl)
    (σ := τ4) ⟨by simp, by simp [τ4], (hc2.setVar (by decide) _).setVar (by decide) _ |>.setVar
      (by decide) _, fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [τ4],
      by simp [τ4]; rfl⟩
  refine ⟨τ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, ?_⟩
  · unfold cmpCost; have : N ≤ 2 * u.length + 6 := by omega
    have := Nat.mul_le_mul_left (stepCost + 4) this
    omega
  · rw [hst, cmpUp_eq _ _ _ (by rw [tupH_length]; omega) (by rw [tupH_length]; omega)]

/-! ### Counting and ranking -/

/-- The jobs below `k` with the tuple of job `j`. -/
def cntUp (u : List ℕ) (j k : ℕ) : ℕ :=
  ((List.range k).filter fun i => cmpL (tupH u i) (tupH u j) == 0).length

/-- `0` once a job below `k` and below `j` has the tuple of job `j`, `1` before. -/
def flUp (u : List ℕ) (j k : ℕ) : ℕ :=
  if (List.range k).any (fun i => decide (i < j) && cmpL (tupH u i) (tupH u j) == 0) then 0 else 1

/-- `1` for a first job. -/
def fsN (u : List ℕ) (j : ℕ) : ℕ := if fstH u j then 1 else 0

/-- The first jobs below `k` with a smaller tuple than job `j`. -/
def rkUp (u : List ℕ) (j k : ℕ) : ℕ := ((List.range k).filter fun i => fstH u i && lessH u i j).length

theorem cntUp_le (u : List ℕ) (j k : ℕ) : cntUp u j k ≤ k :=
  (List.length_filter_le _ _).trans (by simp)

theorem rkUp_le (u : List ℕ) (j k : ℕ) : rkUp u j k ≤ k :=
  (List.length_filter_le _ _).trans (by simp)

theorem flUp_le (u : List ℕ) (j k : ℕ) : flUp u j k ≤ 1 := by unfold flUp; split_ifs <;> omega

theorem fsN_le (u : List ℕ) (j : ℕ) : fsN u j ≤ 1 := by unfold fsN; split_ifs <;> omega

theorem cntH_le (u : List ℕ) (j : ℕ) : cntH u j ≤ u.length :=
  (cntUp_le u j (nA u)).trans (nA_le u)

theorem cntUp_succ (u : List ℕ) (j k : ℕ) :
    cntUp u j (k + 1) = cntUp u j k + (1 - cmpL (tupH u k) (tupH u j)) := by
  unfold cntUp; rw [filter_range_succ]
  by_cases h : cmpL (tupH u k) (tupH u j) = 0
  · simp [h]
  · simp [h]; omega

theorem flUp_succ (u : List ℕ) (j k : ℕ) :
    flUp u j (k + 1) = flUp u j k * (1 - (1 - cmpL (tupH u k) (tupH u j)) * indN (j - k)) := by
  unfold flUp
  rw [List.range_succ, List.any_append, Lax434175Proofs.HighMultiplicityMap.indN_sub]
  by_cases h1 : (List.range k).any (fun i => decide (i < j) && cmpL (tupH u i) (tupH u j) == 0) = true
  · simp [h1]
  · by_cases h2 : cmpL (tupH u k) (tupH u j) = 0 <;> by_cases h3 : k < j
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
    · simp only [h1, h3, if_true, Bool.false_or, List.any_cons, List.any_nil, Bool.or_false]
      simp [h2]; omega
    · simp [h1, h3]

theorem fsN_eq (u : List ℕ) (j : ℕ) : flUp u j (nA u) = fsN u j := by
  unfold flUp fsN fstH
  cases (List.range (nA u)).any (fun i => decide (i < j) && cmpL (tupH u i) (tupH u j) == 0) <;> rfl

theorem rkUp_succ (u : List ℕ) (j k : ℕ) :
    rkUp u j (k + 1) = rkUp u j k + fsN u k * (indN (cntH u j - cntH u k) +
      eqN (cntH u k) (cntH u j) * eqN (cmpL (tupH u k) (tupH u j)) 1) := by
  unfold rkUp; rw [filter_range_succ]
  congr 1
  unfold fsN lessH
  rw [Lax434175Proofs.HighMultiplicityMap.indN_sub, eqN_eq, eqN_eq]
  by_cases h1 : fstH u k = true <;> by_cases h2 : cntH u k < cntH u j <;>
    by_cases h3 : cntH u k = cntH u j <;> by_cases h4 : cmpL (tupH u k) (tupH u j) = 1 <;>
    simp [h1, h2, h3, h4]

/-- **Count job `i` if it has the tuple of job `j`.** -/
theorem run_cntInner (bd : Bd u B) {σ : Env} (h : Ctx u σ) {i j : ℕ} (hi : i < nA u) (hj : j < nA u)
    (hiv : σ.vars "i" = i) (hjv : σ.vars "j" = j) (hc : σ.vars "c" = cntUp u j i)
    (hf : σ.vars "fl" = flUp u j i) :
    ∃ σ', Run B cntInner σ σ' (cmpCost u + 30) ∧ σ'.vars "i" = i + 1 ∧
      σ'.vars "c" = cntUp u j (i + 1) ∧ σ'.vars "fl" = flUp u j (i + 1) := by
  have hn := nA_le u
  have hb := bd.pos
  obtain ⟨σ1, r1, hst⟩ := run_cmp bd h hi hj hiv hjv
  set s := cmpL (tupH u i) (tupH u j)
  have hs2 : s ≤ 2 := cmpL_le_two _ _
  have hi1 : σ1.vars "i" = i := by rw [r1.frame_var "i" (by decide), hiv]
  have hj1 : σ1.vars "j" = j := by rw [r1.frame_var "j" (by decide), hjv]
  have hc1 : σ1.vars "c" = cntUp u j i := by rw [r1.frame_var "c" (by decide), hc]
  have hf1 : σ1.vars "fl" = flUp u j i := by rw [r1.frame_var "fl" (by decide), hf]
  have hcl := cntUp_le u j i
  have hfl := flUp_le u j i
  have r2 : Run B (.assign "e" (.sub (.lit 1) (V "st"))) σ1 (σ1.setVar "e" (1 - s)) 4 :=
    (Run.assign (ev_sub (ev_lit (by omega)) (ev_var hst (by omega)))).mono (by simp)
  set σ2 := σ1.setVar "e" (1 - s)
  have r3 : Run B (.assign "c" (.add (V "c") (V "e"))) σ2 (σ2.setVar "c" (cntUp u j i + (1 - s))) 4 :=
    (Run.assign (ev_add (ev_var (by simp [σ2, hc1]) (by omega)) (ev_var (by simp [σ2]) (by omega))
      (by omega))).mono (by simp)
  set σ3 := σ2.setVar "c" (cntUp u j i + (1 - s))
  have hm : (1 - s) * indN (j - i) ≤ 1 := (mul_le_of_le_one (by omega) _).trans (indN_le _)
  have hm2 : flUp u j i * (1 - (1 - s) * indN (j - i)) ≤ 1 := (mul_le_of_le_one hfl _).trans (by omega)
  have r4 : Run B (.assign "fl" (.mul (V "fl") (.sub (.lit 1) (.mul (V "e") (ind (.sub (V "j") (V "i")))))))
      σ3 (σ3.setVar "fl" (flUp u j i * (1 - (1 - s) * indN (j - i)))) 14 :=
    (Run.assign (ev_mul (ev_var (by simp [σ3, σ2, hf1]) (by omega)) (ev_sub (ev_lit (by omega))
      (ev_mul (ev_var (by simp [σ3, σ2]) (by omega)) (ev_ind (ev_sub (ev_var (by simp [σ3, σ2, hj1])
        (by omega)) (ev_var (by simp [σ3, σ2, hi1]) (by omega))) (by omega)) (by omega))) (by omega))).mono
      (by simp)
  set σ4 := σ3.setVar "fl" (flUp u j i * (1 - (1 - s) * indN (j - i)))
  have r5 := run_incr (B := B) (k := i) "i" (τ := σ4) (by simp [σ4, σ3, σ2, hi1]) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), by simp, ?_, ?_⟩
  · rw [cntUp_succ]; simp [σ4, σ3, s]
  · rw [flUp_succ]; simp [σ4, s]

/-- The cost of the counts for one job. -/
def cntCost (u : List ℕ) : ℕ := (cmpCost u + 34) * u.length + 30

/-- **The count and the first-flag of job `j`.** -/
theorem run_cntBody (bd : Bd u B) {σ : Env} (h : Ctx u σ) {j : ℕ} (hj : j < nA u) (hjv : σ.vars "j" = j)
    (hcn : σ.arrs "cn" = upto u.length j (cntH u)) (hfs : σ.arrs "fs" = upto u.length j (fsN u))
    (hd : σ.vars "d" = ((List.range j).filter (fstH u)).length) :
    ∃ σ', Run B cntBody σ σ' (cntCost u) ∧ σ'.vars "j" = j + 1 ∧ Ctx u σ' ∧
      σ'.arrs "cn" = upto u.length (j + 1) (cntH u) ∧ σ'.arrs "fs" = upto u.length (j + 1) (fsN u) ∧
      σ'.vars "d" = ((List.range (j + 1)).filter (fstH u)).length := by
  have hn := nA_le u
  have hb := bd.pos
  have r1 : Run B (.assign "c" (.lit 0)) σ (σ.setVar "c" 0) 2 := Run.assign (ev_lit (by omega))
  have r2 : Run B (.assign "fl" (.lit 1)) (σ.setVar "c" 0) ((σ.setVar "c" 0).setVar "fl" 1) 2 :=
    Run.assign (ev_lit (by omega))
  set σ2 := (σ.setVar "c" 0).setVar "fl" 1
  obtain ⟨σ3, r3, -, hc3, hj3, hcv, hfv⟩ := run_forLoop (B := B) "i" "n" cntInner (nA u) (cmpCost u + 30)
    (by omega)
    (fun k τ => τ.vars "i" = k ∧ Ctx u τ ∧ τ.vars "j" = j ∧ τ.vars "c" = cntUp u j k ∧
      τ.vars "fl" = flUp u j k)
    (fun k τ h => h.1) (fun k τ h => h.2.1.n)
    (fun k hk τ ⟨hiv, hc, hjv', hcv, hfv⟩ => by
      obtain ⟨τ', r, hi', hc', hf'⟩ := run_cntInner bd hc hk hj hiv hjv' hcv hfv
      exact ⟨τ', r, hi', hc.run r (by decide) (by decide), by rw [r.frame_var "j" (by decide), hjv'],
        hc', hf'⟩)
    (σ := σ2) ⟨by simp, ((h.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _,
      by simp [σ2, hjv], by simp [σ2, cntUp], by simp [σ2, flUp]⟩
  have hw3 : (forLoop "i" "n" cntInner).warrs = [] := by decide
  have ha3 : σ3.arrs = σ.arrs := by rw [r3.frame_arrs_eqOn hw3]; simp [σ2]
  have hd3 : σ3.vars "d" = σ.vars "d" := by rw [r3.frame_var "d" (by decide)]; simp [σ2]
  have hcB := cntH_le u j
  have r4 : Run B (.store "cn" (V "j") (V "c")) σ3 (σ3.setArr "cn" j (cntH u j)) 3 :=
    Run.store (ev_var hj3 (by omega)) (ev_var hcv (by omega)) (by rw [ha3, hcn]; simp; omega)
  set σ4 := σ3.setArr "cn" j (cntH u j)
  have hfB := fsN_le u j
  have hfl3 : σ3.vars "fl" = fsN u j := by rw [hfv, fsN_eq]
  have r5 : Run B (.store "fs" (V "j") (V "fl")) σ4 (σ4.setArr "fs" j (fsN u j)) 3 :=
    Run.store (ev_var (by simp [σ4, hj3]) (by omega)) (ev_var (by simp [σ4, hfl3]) (by omega))
      (by simp [σ4, ha3, hfs]; omega)
  set σ5 := σ4.setArr "fs" j (fsN u j)
  have hdl := List.length_filter_le (fstH u) (List.range j)
  rw [List.length_range] at hdl
  have r6 : Run B (.assign "d" (.add (V "d") (V "fl"))) σ5
      (σ5.setVar "d" (((List.range j).filter (fstH u)).length + fsN u j)) 4 :=
    (Run.assign (ev_add (ev_var (by simp [σ5, σ4, hd3, hd]) (by omega))
      (ev_var (by simp [σ5, σ4, hfl3]) (by omega)) (by omega))).mono (by simp)
  set σ6 := σ5.setVar "d" (((List.range j).filter (fstH u)).length + fsN u j)
  have r7 := run_incr (B := B) (k := j) "j" (τ := σ6) (by simp [σ6, σ5, σ4, hj3]) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_, by simp, ?_, ?_, ?_, ?_⟩
  · have : (cmpCost u + 30 + 4) * nA u ≤ (cmpCost u + 34) * u.length := Nat.mul_le_mul (by omega) hn
    unfold cntCost; omega
  · exact (((hc3.setArr (by decide) _ _).setArr (by decide) _ _).setVar (by decide) _).setVar
      (by decide) _
  · simp only [σ6, σ5, σ4, arrs_setVar, arrs_setArr, if_true, if_neg (show ("cn" : String) ≠ "fs" by decide)]
    rw [ha3, hcn]; exact store_upto (by omega)
  · simp only [σ6, σ5, σ4, arrs_setVar, arrs_setArr, if_true, if_neg (show ("fs" : String) ≠ "cn" by decide)]
    rw [ha3, hfs]; exact store_upto (by omega)
  · simp only [σ6, vars_setVar, if_neg (show ("d" : String) ≠ "j" by decide), if_true]
    rw [filter_range_succ]; rfl

/-- **The counts and the first-flags of all jobs.** -/
theorem run_cnt (bd : Bd u B) {σ : Env} (h : Ctx u σ) (hcn : σ.arrs "cn" = upto u.length 0 (cntH u))
    (hfs : σ.arrs "fs" = upto u.length 0 (fsN u)) (hd : σ.vars "d" = 0) :
    ∃ σ', Run B (forLoop "j" "n" cntBody) σ σ' ((cntCost u + 4) * nA u + 6) ∧ Ctx u σ' ∧
      σ'.arrs "cn" = upto u.length (nA u) (cntH u) ∧ σ'.arrs "fs" = upto u.length (nA u) (fsN u) ∧
      σ'.vars "d" = ddH u := by
  have hn := nA_le u
  have hb := bd.pos
  obtain ⟨σ', r, -, hc, hcn', hfs', hd'⟩ := run_forLoop (B := B) "j" "n" cntBody (nA u) (cntCost u)
    (by omega)
    (fun k τ => τ.vars "j" = k ∧ Ctx u τ ∧ τ.arrs "cn" = upto u.length k (cntH u) ∧
      τ.arrs "fs" = upto u.length k (fsN u) ∧ τ.vars "d" = ((List.range k).filter (fstH u)).length)
    (fun k τ h => h.1) (fun k τ h => h.2.1.n)
    (fun k hk τ ⟨hjv, hc, hcn, hfs, hd⟩ => run_cntBody bd hc hk hjv hcn hfs hd)
    (σ := σ) ⟨by simp, h.setVar (by decide) _, by simp [hcn], by simp [hfs], by simp [hd]⟩
  exact ⟨σ', r, hc, hcn', hfs', hd'⟩

theorem ev_eqE {B : ℕ} {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (h : a + b < B) (h1 : 1 < B) : (eqE e f).evalB B σ = some (eqN a b) :=
  ev_sub (ev_lit h1) (ev_add (ev_sub he hf) (ev_sub hf he) (by omega))

theorem eqN_le (a b : ℕ) : eqN a b ≤ 1 := by unfold eqN; omega

/-- **Count job `i` if it is first with a smaller tuple than job `j`.** -/
theorem run_rkInner (bd : Bd u B) {σ : Env} (h : Ctx u σ)
    (hcn : σ.arrs "cn" = upto u.length (nA u) (cntH u)) (hfs : σ.arrs "fs" = upto u.length (nA u) (fsN u))
    {i j : ℕ} (hi : i < nA u) (hj : j < nA u) (hiv : σ.vars "i" = i) (hjv : σ.vars "j" = j)
    (hr : σ.vars "r" = rkUp u j i) :
    ∃ σ', Run B rkInner σ σ' (cmpCost u + 44) ∧ σ'.vars "i" = i + 1 ∧
      σ'.vars "r" = rkUp u j (i + 1) := by
  have hn := nA_le u
  have hb := bd.pos
  obtain ⟨σ1, r1, hst⟩ := run_cmp bd h hi hj hiv hjv
  set s := cmpL (tupH u i) (tupH u j)
  have hs2 : s ≤ 2 := cmpL_le_two _ _
  have hw1 : cmpCom.warrs = [] := by decide
  have ha1 : σ1.arrs = σ.arrs := r1.frame_arrs_eqOn hw1
  have hi1 : σ1.vars "i" = i := by rw [r1.frame_var "i" (by decide), hiv]
  have hj1 : σ1.vars "j" = j := by rw [r1.frame_var "j" (by decide), hjv]
  have hr1 : σ1.vars "r" = rkUp u j i := by rw [r1.frame_var "r" (by decide), hr]
  have hL2 : nA u ≤ u.length + 2 := by omega
  have hci := cntH_le u i
  have hcj := cntH_le u j
  have r2 : Run B (.assign "ci" (.get "cn" (V "i"))) σ1 (σ1.setVar "ci" (cntH u i)) 3 :=
    (Run.assign (evalB_get (ev_var hi1 (by omega)) (by rw [ha1, hcn]; exact upto_get hi hL2)
      (by omega))).mono (by simp)
  set σ2 := σ1.setVar "ci" (cntH u i)
  have r3 : Run B (.assign "cj" (.get "cn" (V "j"))) σ2 (σ2.setVar "cj" (cntH u j)) 3 :=
    (Run.assign (evalB_get (ev_var (v := j) (by simp [σ2, hj1]) (by omega))
      (by simp only [σ2, arrs_setVar]; rw [ha1, hcn]; exact upto_get hj hL2) (by omega))).mono (by simp)
  set σ3 := σ2.setVar "cj" (cntH u j)
  have hfsi := fsN_le u i
  have hl1 := indN_le (cntH u j - cntH u i)
  have hl2 := eqN_le (cntH u i) (cntH u j)
  have hl3 := eqN_le s 1
  have hl4 : eqN (cntH u i) (cntH u j) * eqN s 1 ≤ 1 := (mul_le_of_le_one hl2 _).trans hl3
  have hl5 : fsN u i * (indN (cntH u j - cntH u i) + eqN (cntH u i) (cntH u j) * eqN s 1) ≤ 2 :=
    (mul_le_of_le_one hfsi _).trans (by omega)
  have hrk := rkUp_le u j i
  have r4 : Run B (.assign "r" (.add (V "r") (.mul (.get "fs" (V "i"))
      (.add (ind (.sub (V "cj") (V "ci"))) (.mul (eqE (V "ci") (V "cj")) (eqE (V "st") (.lit 1)))))))
      σ3 (σ3.setVar "r" (rkUp u j i + fsN u i * (indN (cntH u j - cntH u i) +
        eqN (cntH u i) (cntH u j) * eqN s 1))) 34 :=
    (Run.assign (ev_add (ev_var (by simp [σ3, σ2, hr1]) (by omega))
      (ev_mul (evalB_get (ev_var (v := i) (by simp [σ3, σ2, hi1]) (by omega))
        (by simp only [σ3, σ2, arrs_setVar]; rw [ha1, hfs]; exact upto_get hi hL2) (by omega))
        (ev_add (ev_ind (ev_sub (ev_var (by simp [σ3]) (by omega)) (ev_var (by simp [σ3, σ2]) (by omega)))
          (by omega)) (ev_mul (ev_eqE (ev_var (by simp [σ3, σ2]) (by omega)) (ev_var (by simp [σ3])
            (by omega)) (by omega) (by omega)) (ev_eqE (ev_var (by simp [σ3, σ2, hst]) (by omega))
            (ev_lit (by omega)) (by omega) (by omega)) (by omega)) (by omega)) (by omega))
      (by omega))).mono (by simp [eqE])
  set σ4 := σ3.setVar "r" (rkUp u j i + fsN u i * (indN (cntH u j - cntH u i) +
        eqN (cntH u i) (cntH u j) * eqN s 1))
  have r5 := run_incr (B := B) (k := i) "i" (τ := σ4) (by simp [σ4, σ3, σ2, hi1]) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), by simp, ?_⟩
  rw [rkUp_succ]; simp [σ4, s]

/-- The cost of the rank of one job. -/
def rkCost (u : List ℕ) : ℕ := (cmpCost u + 48) * u.length + 20

/-- **The rank of job `j`.** -/
theorem run_rkBody (bd : Bd u B) {σ : Env} (h : Ctx u σ)
    (hcn : σ.arrs "cn" = upto u.length (nA u) (cntH u)) (hfs : σ.arrs "fs" = upto u.length (nA u) (fsN u))
    {j : ℕ} (hj : j < nA u) (hjv : σ.vars "j" = j) (hrk : σ.arrs "rk" = upto u.length j (rkH u)) :
    ∃ σ', Run B rkBody σ σ' (rkCost u) ∧ σ'.vars "j" = j + 1 ∧ Ctx u σ' ∧
      σ'.arrs "cn" = upto u.length (nA u) (cntH u) ∧ σ'.arrs "fs" = upto u.length (nA u) (fsN u) ∧
      σ'.arrs "rk" = upto u.length (j + 1) (rkH u) := by
  have hn := nA_le u
  have hb := bd.pos
  have r1 : Run B (.assign "r" (.lit 0)) σ (σ.setVar "r" 0) 2 := Run.assign (ev_lit (by omega))
  obtain ⟨σ2, r2, -, hc2, hj2, ha2', hr2⟩ := run_forLoop (B := B) "i" "n" rkInner (nA u) (cmpCost u + 44)
    (by omega)
    (fun k τ => τ.vars "i" = k ∧ Ctx u τ ∧ τ.vars "j" = j ∧ τ.arrs = σ.arrs ∧ τ.vars "r" = rkUp u j k)
    (fun k τ h => h.1) (fun k τ h => h.2.1.n)
    (fun k hk τ ⟨hiv, hc, hjv', hca, hrv⟩ => by
      obtain ⟨τ', r, hi', hr'⟩ := run_rkInner bd hc (by rw [hca, hcn]) (by rw [hca, hfs]) hk hj hiv hjv' hrv
      exact ⟨τ', r, hi', hc.run r (by decide) (by decide), by rw [r.frame_var "j" (by decide), hjv'],
        by rw [r.frame_arrs_eqOn (by decide), hca], hr'⟩)
    (σ := σ.setVar "r" 0) ⟨by simp, (h.setVar (by decide) _).setVar (by decide) _, by simp [hjv],
      by simp, by simp [rkUp]⟩
  have hr3 : σ2.vars "r" = rkH u j := hr2
  have ha2 : σ2.arrs = σ.arrs := ha2'
  have hrB := rkUp_le u j (nA u)
  have r3 : Run B (.store "rk" (V "j") (V "r")) σ2 (σ2.setArr "rk" j (rkH u j)) 3 :=
    Run.store (ev_var hj2 (by omega)) (ev_var hr3 (by unfold rkH; unfold rkUp at hrB; omega))
      (by rw [ha2, hrk]; simp; omega)
  have r4 := run_incr (B := B) (k := j) "j" (τ := σ2.setArr "rk" j (rkH u j)) (by simp [hj2]) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono ?_, by simp, ?_, ?_, ?_, ?_⟩
  · have : (cmpCost u + 44 + 4) * nA u ≤ (cmpCost u + 48) * u.length := Nat.mul_le_mul (by omega) hn
    unfold rkCost; omega
  · exact (hc2.setArr (by decide) _ _).setVar (by decide) _
  · simp [ha2, hcn]
  · simp [ha2, hfs]
  · simp only [arrs_setVar, arrs_setArr, if_true]
    rw [ha2, hrk]; exact store_upto (by omega)

/-- **The ranks of all jobs.** -/
theorem run_rk (bd : Bd u B) {σ : Env} (h : Ctx u σ)
    (hcn : σ.arrs "cn" = upto u.length (nA u) (cntH u)) (hfs : σ.arrs "fs" = upto u.length (nA u) (fsN u))
    (hrk : σ.arrs "rk" = upto u.length 0 (rkH u)) :
    ∃ σ', Run B (forLoop "j" "n" rkBody) σ σ' ((rkCost u + 4) * nA u + 6) ∧ Ctx u σ' ∧
      σ'.arrs "cn" = upto u.length (nA u) (cntH u) ∧ σ'.arrs "fs" = upto u.length (nA u) (fsN u) ∧
      σ'.arrs "rk" = upto u.length (nA u) (rkH u) := by
  have hn := nA_le u
  have hb := bd.pos
  obtain ⟨σ', r, -, hc, hcn', hfs', hrk'⟩ := run_forLoop (B := B) "j" "n" rkBody (nA u) (rkCost u)
    (by omega)
    (fun k τ => τ.vars "j" = k ∧ Ctx u τ ∧ τ.arrs "cn" = upto u.length (nA u) (cntH u) ∧
      τ.arrs "fs" = upto u.length (nA u) (fsN u) ∧ τ.arrs "rk" = upto u.length k (rkH u))
    (fun k τ h => h.1) (fun k τ h => h.2.1.n)
    (fun k hk τ ⟨hjv, hc, hcn, hfs, hrk⟩ => run_rkBody bd hc hcn hfs hk hjv hrk)
    (σ := σ) ⟨by simp, h.setVar (by decide) _, by simp [hcn], by simp [hfs], by simp [hrk]⟩
  exact ⟨σ', r, hc, hcn', hfs', hrk'⟩

/-! ### Writing -/

/-- **Write entry `k` of the tuple of job `j`.** -/
theorem run_wtStep (bd : Bd u B) {σ : Env} (h : Ctx u σ) {j k : ℕ} (hj : j < nA u)
    (hk : k < lnH u j + 3) (hP : σ.vars "P1" = posA u j + 1) (hN : σ.vars "N1" = lnH u j)
    (hO : σ.vars "O1" = obH u + 3 * j) (hkv : σ.vars "k" = k) :
    ∃ σ', Run B wtStep σ σ' 42 ∧ σ'.vars "k" = k + 1 ∧ σ'.out = σ.out ++ [u.getD (idxH u j k) 0] := by
  have hL := lnH_le u j
  have hb := bd.pos
  have r1 := run_readT bd h (P := "P1") (N := "N1") (O := "O1") (dst := "va") hj (k := k) (by omega)
    hP hN hO hkv (by decide) (by decide) (by decide)
  set σ1 := ((σ.setVar "h" (indN (lnH u j - k))).setVar "x" (idxH u j k)).setVar "va"
    (u.getD (idxH u j k) 0)
  have r2 : Run B (.write (V "va")) σ1 { σ1 with out := σ1.out ++ [u.getD (idxH u j k) 0] } 2 :=
    Run.write (ev_var (by simp [σ1]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
  have r3 := run_incr (B := B) (k := k) "k" (τ := { σ1 with out := σ1.out ++ [u.getD (idxH u j k) 0] })
    (by simp [σ1, hkv]) (by omega)
  exact ⟨_, (r1.seq (r2.seq r3)).mono (by norm_num), by simp, by simp [σ1]⟩

/-- The cost of writing a tuple. -/
def wtCost (u : List ℕ) : ℕ := 46 * (u.length + 3) + 40

/-- **Write the tuple of job `j` with its number and its length in front.** -/
theorem run_writeTup (bd : Bd u B) {σ : Env} (h : Ctx u σ)
    (hcn : σ.arrs "cn" = upto u.length (nA u) (cntH u)) {j : ℕ} (hj : j < nA u) (hjv : σ.vars "j" = j) :
    ∃ σ', Run B writeTup σ σ' (wtCost u) ∧
      σ'.out = σ.out ++ ((lnH u j + 4) :: cntH u j :: tupH u j) := by
  have hn := nA_le u
  have hL := lnH_le u j
  have hb := bd.pos
  have r1 := run_setupT bd h (t := "j") (P := "P1") (N := "N1") (O := "O1") (T := "T1") hj hjv
    (by decide) (by decide) (by decide) (by decide) (by decide)
  set σ1 := (((σ.setVar "P1" (posA u j + 1)).setVar "N1" (lnH u j)).setVar "O1" (obH u + 3 * j)).setVar
    "T1" (lnH u j + 3)
  have hc1 : Ctx u σ1 :=
    (((h.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
  have r2 : Run B (.write (.add (V "N1") (.lit 4))) σ1 { σ1 with out := σ1.out ++ [lnH u j + 4] } 4 :=
    (Run.write (ev_add (ev_var (by simp [σ1]) (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
  set σ2 : Env := { σ1 with out := σ1.out ++ [lnH u j + 4] }
  have hcj := cntH_le u j
  have r3 : Run B (.write (.get "cn" (V "j"))) σ2 { σ2 with out := σ2.out ++ [cntH u j] } 3 :=
    (Run.write (evalB_get (ev_var (v := j) (by simp [σ2, σ1, hjv]) (by omega))
      (by show (σ1.arrs "cn")[j]? = _; simp only [σ1, arrs_setVar]; rw [hcn]; exact upto_get hj (by omega))
      (by omega))).mono (by simp)
  set σ3 : Env := { σ2 with out := σ2.out ++ [cntH u j] }
  have hc3 : Ctx u σ3 := (hc1.out _).out _
  obtain ⟨σ4, r4, -, -, -, -, -, -, ho4⟩ := run_forLoop (B := B) "k" "T1" wtStep (lnH u j + 3) 42
    (by omega)
    (fun k τ => τ.vars "k" = k ∧ τ.vars "T1" = lnH u j + 3 ∧ Ctx u τ ∧ τ.vars "P1" = posA u j + 1 ∧
      τ.vars "N1" = lnH u j ∧ τ.vars "O1" = obH u + 3 * j ∧
      τ.out = σ3.out ++ (List.range k).map fun k => u.getD (idxH u j k) 0)
    (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hkv, hT, hc, hP, hN, hO, ho⟩ => by
      obtain ⟨τ', r, hk', ho'⟩ := run_wtStep bd hc hj hk hP hN hO hkv
      refine ⟨τ', r, hk', by rw [r.frame_var "T1" (by decide), hT], hc.run r (by decide) (by decide),
        by rw [r.frame_var "P1" (by decide), hP], by rw [r.frame_var "N1" (by decide), hN],
        by rw [r.frame_var "O1" (by decide), hO], ?_⟩
      rw [ho', ho, List.range_succ, List.map_append, List.append_assoc]; rfl)
    (σ := σ3) ⟨by simp, by simp [σ3, σ2, σ1], hc3.setVar (by decide) _, by simp [σ3, σ2, σ1],
      by simp [σ3, σ2, σ1], by simp [σ3, σ2, σ1], by simp⟩
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono ?_, ?_⟩
  · unfold wtCost
    have : (42 + 4) * (lnH u j + 3) ≤ 46 * (u.length + 3) := by omega
    omega
  · rw [ho4]; simp [σ3, σ2, σ1, tupH]

theorem fs_rk_iff (u : List ℕ) (j r : ℕ) :
    fsN u j * (rkH u j + 1) = r + 1 ↔ (fstH u j && rkH u j == r) = true := by
  unfold fsN; cases fstH u j <;> simp

/-- The cost of one job in the writing of one rank. -/
def outCost (u : List ℕ) : ℕ := wtCost u + 20

/-- **Write the tuple of job `j` if it is first with rank `r`.** -/
theorem run_outInner (bd : Bd u B) {σ : Env} (h : Ctx u σ)
    (hcn : σ.arrs "cn" = upto u.length (nA u) (cntH u)) (hfs : σ.arrs "fs" = upto u.length (nA u) (fsN u))
    (hrk : σ.arrs "rk" = upto u.length (nA u) (rkH u)) {r j : ℕ} (hr : r < nA u) (hj : j < nA u)
    (hrv : σ.vars "r" = r) (hjv : σ.vars "j" = j) :
    ∃ σ', Run B outInner σ σ' (outCost u) ∧ σ'.vars "j" = j + 1 ∧ σ'.out = σ.out ++ outH u r j := by
  have hn := nA_le u
  have hb := bd.pos
  have hfj := fsN_le u j
  have hrkj : rkH u j ≤ u.length := (rkUp_le u j (nA u)).trans hn
  have hm : fsN u j * (rkH u j + 1) ≤ rkH u j + 1 := mul_le_of_le_one hfj _
  have hcond : (Cond.eq (.mul (.get "fs" (V "j")) (.add (.get "rk" (V "j")) (.lit 1))) (.add (V "r") (.lit 1))).evalB
      B σ = some (fsN u j * (rkH u j + 1) == r + 1) :=
    evalB_condEq (ev_mul (evalB_get (ev_var hjv (by omega)) (by rw [hfs]; exact upto_get hj (by omega))
      (by omega)) (ev_add (evalB_get (ev_var hjv (by omega)) (by rw [hrk]; exact upto_get hj (by omega))
        (by omega)) (ev_lit (by omega)) (by omega)) (by omega)) (ev_add (ev_var hrv (by omega))
      (ev_lit (by omega)) (by omega))
  by_cases hc : (fstH u j && rkH u j == r) = true
  · obtain ⟨σ1, r1, ho1⟩ := run_writeTup bd h hcn hj hjv
    have r2 : Run B (.ite (.eq (.mul (.get "fs" (V "j")) (.add (.get "rk" (V "j")) (.lit 1)))
        (.add (V "r") (.lit 1))) writeTup .skip) σ σ1 (wtCost u + 12) :=
      (Run.ite_true (by rw [hcond]; simp [(fs_rk_iff u j r).mpr hc]) r1).mono (by simp; omega)
    have r3 := run_incr (B := B) (k := j) "j" (τ := σ1) (by rw [r1.frame_var "j" (by decide), hjv])
      (by omega)
    refine ⟨_, (r2.seq r3).mono (by unfold outCost; omega), by simp, ?_⟩
    rw [show (σ1.setVar "j" (j + 1)).out = σ1.out from rfl, ho1, outH, if_pos hc]
  · have r2 : Run B (.ite (.eq (.mul (.get "fs" (V "j")) (.add (.get "rk" (V "j")) (.lit 1)))
        (.add (V "r") (.lit 1))) writeTup .skip) σ σ 13 :=
      (Run.ite_false (by rw [hcond]; simpa using fun h => hc ((fs_rk_iff u j r).mp h)) Run.skip).mono
        (by simp)
    have r3 := run_incr (B := B) (k := j) "j" (τ := σ) hjv (by omega)
    refine ⟨_, (r2.seq r3).mono (by unfold outCost; omega), by simp, ?_⟩
    rw [show (σ.setVar "j" (j + 1)).out = σ.out from rfl, outH, if_neg hc, List.append_nil]

/-- The cost of writing one rank. -/
def outBodyCost (u : List ℕ) : ℕ := (outCost u + 4) * u.length + 10

/-- **Write the tuple of rank `r`.** -/
theorem run_outBody (bd : Bd u B) {σ : Env} (h : Ctx u σ)
    (hcn : σ.arrs "cn" = upto u.length (nA u) (cntH u)) (hfs : σ.arrs "fs" = upto u.length (nA u) (fsN u))
    (hrk : σ.arrs "rk" = upto u.length (nA u) (rkH u)) {r : ℕ} (hr : r < nA u) (hrv : σ.vars "r" = r) :
    ∃ σ', Run B outBody σ σ' (outBodyCost u) ∧ σ'.vars "r" = r + 1 ∧ Ctx u σ' ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ++ (List.range (nA u)).flatMap (outH u r) := by
  have hn := nA_le u
  have hb := bd.pos
  obtain ⟨σ1, r1, -, hc1, -, hr1, ho1⟩ := run_forLoop (B := B) "j" "n" outInner (nA u) (outCost u)
    (by omega)
    (fun k τ => τ.vars "j" = k ∧ Ctx u τ ∧ τ.arrs = σ.arrs ∧ τ.vars "r" = r ∧
      τ.out = σ.out ++ (List.range k).flatMap (outH u r))
    (fun k τ h => h.1) (fun k τ h => h.2.1.n)
    (fun k hk τ ⟨hjv, hc, ha, hrv', ho⟩ => by
      obtain ⟨τ', r', hj', ho'⟩ := run_outInner bd hc (by rw [ha, hcn]) (by rw [ha, hfs]) (by rw [ha, hrk])
        hr hk hrv' hjv
      refine ⟨τ', r', hj', hc.run r' (by decide) (by decide), by rw [r'.frame_arrs_eqOn (by decide), ha],
        by rw [r'.frame_var "r" (by decide), hrv'], ?_⟩
      rw [ho', ho, List.range_succ, List.flatMap_append, List.append_assoc]; simp)
    (σ := σ) ⟨by simp, h.setVar (by decide) _, by simp, by simp [hrv], by simp⟩
  have r2 := run_incr (B := B) (k := r) "r" (τ := σ1) hr1 (by omega)
  refine ⟨_, (r1.seq r2).mono ?_, by simp, hc1.setVar (by decide) _, ?_, ho1⟩
  · have : (outCost u + 4) * nA u ≤ (outCost u + 4) * u.length := Nat.mul_le_mul_left _ hn
    unfold outBodyCost; omega
  · rw [show (σ1.setVar "r" (r + 1)).arrs = σ1.arrs from rfl, r1.frame_arrs_eqOn (by decide)]

/-- **Write the tuples of all ranks.** -/
theorem run_out (bd : Bd u B) {σ : Env} (h : Ctx u σ)
    (hcn : σ.arrs "cn" = upto u.length (nA u) (cntH u)) (hfs : σ.arrs "fs" = upto u.length (nA u) (fsN u))
    (hrk : σ.arrs "rk" = upto u.length (nA u) (rkH u)) :
    ∃ σ', Run B (forLoop "r" "n" outBody) σ σ' ((outBodyCost u + 4) * nA u + 6) ∧ Ctx u σ' ∧
      σ'.out = σ.out ++ (List.range (nA u)).flatMap (fun r => (List.range (nA u)).flatMap (outH u r)) := by
  have hn := nA_le u
  have hb := bd.pos
  obtain ⟨σ', r, -, hc, -, ho⟩ := run_forLoop (B := B) "r" "n" outBody (nA u) (outBodyCost u) (by omega)
    (fun k τ => τ.vars "r" = k ∧ Ctx u τ ∧ τ.arrs = σ.arrs ∧
      τ.out = σ.out ++ (List.range k).flatMap (fun r => (List.range (nA u)).flatMap (outH u r)))
    (fun k τ h => h.1) (fun k τ h => h.2.1.n)
    (fun k hk τ ⟨hrv, hc, ha, ho⟩ => by
      obtain ⟨τ', r', hr', hc', ha', ho'⟩ := run_outBody bd hc (by rw [ha, hcn]) (by rw [ha, hfs])
        (by rw [ha, hrk]) hk hrv
      refine ⟨τ', r', hr', hc', by rw [ha', ha], ?_⟩
      rw [ho', ho, List.range_succ, List.flatMap_append, List.append_assoc]; simp)
    (σ := σ) ⟨by simp, h.setVar (by decide) _, by simp, by simp⟩
  exact ⟨σ', r, hc, ho⟩

/-- **Copy the two blocks.** -/
theorem run_mid (bd : Bd u B) {σ : Env} (h : Ctx u σ) (hz : σ.vars "z" = obH u - posA u (nA u)) :
    ∃ σ', Run B (forLoop "k" "z" midBody) σ σ' (21 * u.length + 6) ∧ Ctx u σ' ∧
      σ'.out = σ.out ++ midH u := by
  have hn := nA_le u
  have hb := bd.pos
  have hob := obH_le u
  obtain ⟨σ', r, -, hc, -, ho⟩ := run_forLoop (B := B) "k" "z" midBody (obH u - posA u (nA u)) 17
    (by omega)
    (fun k τ => τ.vars "k" = k ∧ Ctx u τ ∧ τ.vars "z" = obH u - posA u (nA u) ∧
      τ.out = σ.out ++ (List.range k).map fun k => u.getD (posA u (nA u) + k) 0)
    (fun k τ h => h.1) (fun k τ h => h.2.2.1)
    (fun k hk τ ⟨hkv, hc, hzv, ho⟩ => by
      have r1 := ev_rd (B := B) hc.a hc.L (e := .add (V "q") (V "k"))
        (ev_add (ev_var hc.q (bd.posA le_rfl 0 (by omega))) (ev_var hkv (by omega))
          (bd.posA le_rfl k (by omega))) bd.M bd.Lt "v"
      set τ1 := τ.setVar "v" (u.getD (posA u (nA u) + k) 0)
      have r2 : Run B (.write (V "v")) τ1 { τ1 with out := τ1.out ++ [u.getD (posA u (nA u) + k) 0] } 2 :=
        Run.write (ev_var (by simp [τ1]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
      have r3 := run_incr (B := B) (k := k) "k"
        (τ := { τ1 with out := τ1.out ++ [u.getD (posA u (nA u) + k) 0] }) (by simp [τ1, hkv]) (by omega)
      refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), by simp, ((hc.setVar (by decide) _).out _).setVar
        (by decide) _, by simp [τ1, hzv], ?_⟩
      simp [τ1, ho, List.range_succ])
    (σ := σ) ⟨by simp, h.setVar (by decide) _, by simp [hz], by simp⟩
  refine ⟨σ', r.mono ?_, hc, by rw [ho]; rfl⟩
  have : obH u - posA u (nA u) ≤ u.length := by omega
  omega

/-! ### Locating the records -/

/-- What holds before the records are located. -/
structure Pre (u : List ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = arrW u
  L : τ.vars "L" = u.length
  n : τ.vars "n" = nA u

theorem Pre.setVar {τ : Env} (h : Pre u τ) {y : String} (h1 : y ≠ "L") (h2 : y ≠ "n") (w : ℕ) :
    Pre u (τ.setVar y w) :=
  ⟨by simp [h.a], by simp [h1.symm, h.L], by simp [h2.symm, h.n]⟩

theorem Pre.setArr {τ : Env} (h : Pre u τ) {b : String} (hb : b ≠ "a") (i w : ℕ) :
    Pre u (τ.setArr b i w) :=
  ⟨by simp [hb.symm, h.a], by simp [h.L], by simp [h.n]⟩

/-- **Locate the records.** -/
theorem run_pos (bd : Bd u B) {σ : Env} (h : Pre u σ) (hq : σ.vars "q" = 3)
    (hps : σ.arrs "ps" = upto u.length 0 (posA u)) (hln : σ.arrs "ln" = upto u.length 0 (lnH u)) :
    ∃ σ', Run B (forLoop "j" "n" posBody) σ σ' (33 * u.length + 6) ∧ Pre u σ' ∧
      σ'.vars "q" = posA u (nA u) ∧ σ'.arrs "ps" = upto u.length (nA u) (posA u) ∧
      σ'.arrs "ln" = upto u.length (nA u) (lnH u) := by
  have hn := nA_le u
  have hb := bd.pos
  obtain ⟨σ', r, -, hc, hq', hps', hln'⟩ := run_forLoop (B := B) "j" "n" posBody (nA u) 29 (by omega)
    (fun k τ => τ.vars "j" = k ∧ Pre u τ ∧ τ.vars "q" = posA u k ∧
      τ.arrs "ps" = upto u.length k (posA u) ∧ τ.arrs "ln" = upto u.length k (lnH u))
    (fun k τ h => h.1) (fun k τ h => h.2.1.n)
    (fun k hk τ ⟨hjv, hc, hqv, hpv, hlv⟩ => by
      have hp := bd.posA hk.le 0 (by omega)
      have r1 : Run B (.store "ps" (V "j") (V "q")) τ (τ.setArr "ps" k (posA u k)) 3 :=
        Run.store (ev_var hjv (by omega)) (ev_var hqv (by omega)) (by rw [hpv]; simp; omega)
      set τ1 := τ.setArr "ps" k (posA u k)
      have hc1 : Pre u τ1 := hc.setArr (by decide) _ _
      have r2 := ev_rd (B := B) hc1.a hc1.L (e := V "q") (ev_var (v := posA u k) (by simp [τ1, hqv])
        (by omega)) bd.M
        bd.Lt "v"
      set τ2 := τ1.setVar "v" (u.getD (posA u k) 0)
      have hv : u.getD (posA u k) 0 ≤ mx u := getD_le_max u _
      have r3 : Run B (minTo "c" "v" "L") τ2 (τ2.setVar "c" (lnH u k)) 6 :=
        run_minTo (by simp [τ2]) (by simp [τ2, hc1.L]) (by omega) (by omega)
      set τ3 := τ2.setVar "c" (lnH u k)
      have hlk := lnH_le u k
      have r4 : Run B (.store "ln" (V "j") (V "c")) τ3 (τ3.setArr "ln" k (lnH u k)) 3 :=
        Run.store (ev_var (by simp [τ3, τ2, τ1, hjv]) (by omega)) (ev_var (by simp [τ3]) (by omega))
          (by simp [τ3, τ2, τ1, hlv]; omega)
      set τ4 := τ3.setArr "ln" k (lnH u k)
      have hp1 := bd.posA (show k + 1 ≤ nA u by omega) 0 (by omega)
      rw [posA_succ] at hp1
      have r5 : Run B (.assign "q" (.add (.add (V "q") (.lit 1)) (V "v"))) τ4
          (τ4.setVar "q" (posA u (k + 1))) 6 := by
        rw [posA_succ]
        exact (Run.assign (ev_add (ev_add (ev_var (by simp [τ4, τ3, τ2, τ1, hqv]) (by omega))
          (ev_lit (by omega)) (by omega)) (ev_var (by simp [τ4, τ3, τ2]) (by omega)) (by omega))).mono
          (by simp)
      set τ5 := τ4.setVar "q" (posA u (k + 1))
      have r6 := run_incr (B := B) (k := k) "j" (τ := τ5) (by simp [τ5, τ4, τ3, τ2, τ1, hjv]) (by omega)
      refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by simp), by simp, ?_,
        by simp [τ5], ?_, ?_⟩
      · exact ((((hc1.setVar (by decide) (by decide) _).setVar (by decide) (by decide) _).setArr
          (by decide) _ _).setVar (by decide) (by decide) _).setVar (by decide) (by decide) _
      · simp only [τ5, τ4, τ3, τ2, τ1, arrs_setVar, arrs_setArr, if_true,
          if_neg (show ("ps" : String) ≠ "ln" by decide)]
        rw [hpv]; exact store_upto (by omega)
      · simp only [τ5, τ4, τ3, τ2, τ1, arrs_setVar, arrs_setArr, if_true,
          if_neg (show ("ln" : String) ≠ "ps" by decide)]
        rw [hlv]; exact store_upto (by omega))
    (σ := σ) ⟨by simp, h.setVar (by decide) (by decide) _, by simp [hq, posA], by simp [hps],
      by simp [hln]⟩
  exact ⟨σ', r.mono (by have := Nat.mul_le_mul_left 33 hn; omega), hc, hq', hps', hln'⟩

end Runs

/-! ### Polynomial time -/

/-- The cost bound. -/
def cost (u : List ℕ) : ℕ := 2000 * (u.length + 1) ^ 3

theorem cost_le (u : List ℕ) :
    13 * u.length + 5 + (2 * (Expr.lit 1).size + 5 + (6 + (2 + (33 * u.length + 6 + (8 + (2 +
      ((cntCost u + 4) * nA u + 6 + ((rkCost u + 4) * nA u + 6 + (2 + (2 * (Expr.lit 1).size + 5 +
      (2 + (2 * (Expr.lit 2).size + 5 + (2 + (2 + ((outBodyCost u + 4) * nA u + 6 + (4 +
      (21 * u.length + 6 + (2 * ((V "L").sub (Expr.lit 2)).size + 5 +
      (2 + (2 * ((V "L").sub (Expr.lit 1)).size + 5 + 2)))))))))))))))))))) ≤ cost u := by
  have hn := nA_le u
  have h1 : (cntCost u + 4) * nA u ≤ (cntCost u + 4) * u.length := Nat.mul_le_mul_left _ hn
  have h2 : (rkCost u + 4) * nA u ≤ (rkCost u + 4) * u.length := Nat.mul_le_mul_left _ hn
  have h3 : (outBodyCost u + 4) * nA u ≤ (outBodyCost u + 4) * u.length := Nat.mul_le_mul_left _ hn
  have e1 : (cntCost u + 4) * u.length = 288 * (u.length * u.length * u.length) +
      946 * (u.length * u.length) + 34 * u.length := by unfold cntCost cmpCost stepCost; ring
  have e2 : (rkCost u + 4) * u.length = 288 * (u.length * u.length * u.length) +
      960 * (u.length * u.length) + 24 * u.length := by unfold rkCost cmpCost stepCost; ring
  have e3 : (outBodyCost u + 4) * u.length = 46 * (u.length * u.length * u.length) +
      202 * (u.length * u.length) + 14 * u.length := by unfold outBodyCost outCost wtCost; ring
  have e4 : cost u = 2000 * (u.length * u.length * u.length) +
      6000 * (u.length * u.length) + 6000 * u.length + 2000 := by unfold cost; ring
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  rw [e4]
  simp only [size_lit, size_sub, size_var]
  generalize (cntCost u + 4) * nA u = X1 at h1 ⊢
  generalize (rkCost u + 4) * nA u = X2 at h2 ⊢
  generalize (outBodyCost u + 4) * nA u = X3 at h3 ⊢
  generalize u.length * u.length * u.length = L3 at h1 h2 h3 ⊢
  generalize u.length * u.length = L2 at h1 h2 h3 ⊢
  clear e1 e2 e3 e4 hn
  linarith

/-- **The run of the program.** -/
theorem run_com (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndCW u) com (initEnv ext (u.length :: u)) σ'
      (cost u) ∧ σ'.out = hmWord u := by
  have bd : Bd u (bndCW u) := bd_of le_rfl
  set B := bndCW u
  have hb := bd.pos
  have hn := nA_le u
  obtain ⟨σ2, r1, ha, hL2, hout2, -, harr⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) bd.M) (by omega)
  refine ⟨fun _ => u.length + 2, ?_⟩
  have r2 := ev_rd (B := B) ha hL2 (e := .lit 1) (evalB_lit (by omega)) bd.M bd.Lt "c"
  set s2 := σ2.setVar "c" (u.getD 1 0)
  have r3 : Run B (minTo "n" "c" "L") s2 (s2.setVar "n" (nA u)) 6 :=
    run_minTo (by simp [s2]) (by simp [s2, hL2]) (lt_of_le_of_lt (getD_le_max u _) bd.M) bd.Lt
  set s3 := s2.setVar "n" (nA u)
  have r4 : Run B (.assign "q" (.lit 3)) s3 (s3.setVar "q" 3) 2 := Run.assign (ev_lit (by omega))
  set s4 := s3.setVar "q" 3
  have hp4 : Pre u s4 := ⟨by simp [s4, s3, s2, ha], by simp [s4, s3, s2, hL2], by simp [s4, s3]⟩
  have hz : ∀ b, b ≠ "a" → ∀ g : ℕ → ℕ, s4.arrs b = upto u.length 0 g := fun b hb g => by
    simp only [s4, s3, s2, arrs_setVar]; rw [harr b hb]; exact upto_zero _ _
  obtain ⟨s5, r5, hp5, hq5, hps5, hln5⟩ := run_pos bd hp4 (by simp [s4]) (hz "ps" (by decide) _)
    (hz "ln" (by decide) _)
  have r6 : Run B (.assign "o" (.sub (.sub (V "L") (.lit 2)) (.mul (.lit 3) (V "n")))) s5
      (s5.setVar "o" (obH u)) 8 :=
    (Run.assign (ev_sub (ev_sub (ev_var hp5.L (by omega)) (ev_lit (by omega)))
      (ev_mul (ev_lit (by omega)) (ev_var hp5.n (by omega)) (by omega)))).mono (by simp)
  set s6 := s5.setVar "o" (obH u)
  have hc6 : Ctx u s6 := ⟨by simp [s6, hp5.a], by simp [s6, hp5.L], by simp [s6, hp5.n],
    by simp [s6, hq5], by simp [s6], by simp [s6, hps5], by simp [s6, hln5]⟩
  have r7 : Run B (.assign "d" (.lit 0)) s6 (s6.setVar "d" 0) 2 := Run.assign (ev_lit (by omega))
  set s7 := s6.setVar "d" 0
  obtain ⟨s8, r8, hc8, hcn8, hfs8, hd8⟩ := run_cnt bd (hc6.setVar (y := "d") (by decide) 0)
    (by simp only [s6, arrs_setVar]; rw [r5.frame_arr "cn" (by decide)]; exact hz "cn" (by decide) _)
    (by simp only [s6, arrs_setVar]; rw [r5.frame_arr "fs" (by decide)]; exact hz "fs" (by decide) _)
    (by simp)
  obtain ⟨s9, r9, hc9, hcn9, hfs9, hrk9⟩ := run_rk bd hc8 hcn8 hfs8
    (by rw [r8.frame_arr "rk" (by decide)]; simp only [s6, arrs_setVar];
        rw [r5.frame_arr "rk" (by decide)]; exact hz "rk" (by decide) _)
  have hd9 : s9.vars "d" = ddH u := by rw [r9.frame_var "d" (by decide), hd8]
  have ho9 : s9.out = [] := by
    rw [r9.out_eq (by decide), r8.out_eq (by decide)]
    simp only [s6, out_setVar]
    rw [r5.out_eq (by decide)]; simp [s4, s3, s2, hout2]
  have r10 : Run B (.write (.lit 1)) s9 { s9 with out := s9.out ++ [1] } 2 := Run.write (ev_lit (by omega))
  set s10 : Env := { s9 with out := s9.out ++ [1] }
  have hc10 : Ctx u s10 := hc9.out _
  have r11 := ev_rd (B := B) hc10.a hc10.L (e := .lit 1) (evalB_lit (by omega)) bd.M bd.Lt "v"
  set s11 := s10.setVar "v" (u.getD 1 0)
  have r12 : Run B (.write (V "v")) s11 { s11 with out := s11.out ++ [u.getD 1 0] } 2 :=
    Run.write (ev_var (by simp [s11]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
  set s12 : Env := { s11 with out := s11.out ++ [u.getD 1 0] }
  have hc12 : Ctx u s12 := (hc10.setVar (by decide) _).out _
  have r13 := ev_rd (B := B) hc12.a hc12.L (e := .lit 2) (evalB_lit (by omega)) bd.M bd.Lt "v"
  set s13 := s12.setVar "v" (u.getD 2 0)
  have r14 : Run B (.write (V "v")) s13 { s13 with out := s13.out ++ [u.getD 2 0] } 2 :=
    Run.write (ev_var (by simp [s13]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
  set s14 : Env := { s13 with out := s13.out ++ [u.getD 2 0] }
  have hdd : ddH u ≤ nA u := (List.length_filter_le _ _).trans (by simp)
  have r15 : Run B (.write (V "d")) s14 { s14 with out := s14.out ++ [ddH u] } 2 :=
    Run.write (ev_var (by simp [s14, s13, s12, s11, s10, hd9]) (by omega))
  set s15 : Env := { s14 with out := s14.out ++ [ddH u] }
  have hc15 : Ctx u s15 := ((hc12.setVar (by decide) _).out _).out _
  obtain ⟨s16, r16, hc16, ho16⟩ := run_out bd hc15 (by simp [s15, s14, s13, s12, s11, s10, hcn9])
    (by simp [s15, s14, s13, s12, s11, s10, hfs9]) (by simp [s15, s14, s13, s12, s11, s10, hrk9])
  have r17 : Run B (.assign "z" (.sub (V "o") (V "q"))) s16 (s16.setVar "z" (obH u - posA u (nA u))) 4 :=
    (Run.assign (ev_sub (ev_var hc16.o (by have := obH_le u; omega))
      (ev_var hc16.q (bd.posA le_rfl 0 (by omega))))).mono (by simp)
  set s17 := s16.setVar "z" (obH u - posA u (nA u))
  obtain ⟨s18, r18, hc18, ho18⟩ := run_mid bd (hc16.setVar (y := "z") (by decide) (obH u - posA u (nA u)))
    (by simp)
  have r19 := ev_rd (B := B) hc18.a hc18.L (e := .sub (V "L") (.lit 2))
    (ev_sub (ev_var hc18.L bd.Lt) (ev_lit (by omega))) bd.M bd.Lt "v"
  set s19 := s18.setVar "v" (u.getD (u.length - 2) 0)
  have r20 : Run B (.write (V "v")) s19 { s19 with out := s19.out ++ [u.getD (u.length - 2) 0] } 2 :=
    Run.write (ev_var (by simp [s19]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
  set s20 : Env := { s19 with out := s19.out ++ [u.getD (u.length - 2) 0] }
  have hc20 : Ctx u s20 := (hc18.setVar (by decide) _).out _
  have r21 := ev_rd (B := B) hc20.a hc20.L (e := .sub (V "L") (.lit 1))
    (ev_sub (ev_var hc20.L bd.Lt) (ev_lit (by omega))) bd.M bd.Lt "v"
  set s21 := s20.setVar "v" (u.getD (u.length - 1) 0)
  have r22 : Run B (.write (V "v")) s21 { s21 with out := s21.out ++ [u.getD (u.length - 1) 0] } 2 :=
    Run.write (ev_var (by simp [s21]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq
    (r12.seq (r13.seq (r14.seq (r15.seq (r16.seq (r17.seq (r18.seq (r19.seq (r20.seq (r21.seq
    r22))))))))))))))))))))).mono ?_, ?_⟩
  · exact cost_le u
  · show s21.out ++ [u.getD (u.length - 1) 0] = hmWord u
    simp only [s21, s20, s19, out_setVar]
    rw [ho18]
    simp only [out_setVar]
    rw [ho16]
    simp only [s15, s14, s13, s12, s11, s10, out_setVar, ho9]
    simp [hmWord]

/-- A run writes only values below the bound. -/
theorem out_lt {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    (∀ v ∈ σ.out, v < B) → ∀ v ∈ σ'.out, v < B := by
  induction h with
  | skip => exact id
  | assign _ => exact id
  | store _ _ _ => exact id
  | seq _ _ ih ih' => exact fun h => ih' (ih h)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact fun h => ih' (ih h)
  | while_false _ => exact id
  | read _ => exact id
  | write he =>
    intro h v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact h v hv
    · rw [List.mem_singleton.mp hv]; exact Expr.lt_of_evalB he

theorem hmWord_lt (u : List ℕ) : ∀ v ∈ hmWord u, v < bndCW u := by
  obtain ⟨ext, σ', ⟨k, -, hb⟩, ho⟩ := run_com u
  rw [← ho]
  exact out_lt hb (by simp [initEnv])

/-- **The word map is polynomial.** -/
theorem hmWord_polytime : Lax759944.RamPolytime.RamPolytime hmWord := by
  refine ramPolytime_of_runs layout com hmWord bndCW cost 20001 3 com_ok
    (fun u v hv => ?_) run_com (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have : u.length + mx u + 8 ≤ (u.length + mx u + 8) ^ 2 := Nat.le_self_pow (by norm_num) _
    unfold bndCW
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bndCW; have : 1 ≤ (u.length + mx u + 8) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit8 u 30 (by norm_num)
    have hb3 : bitSize u + 1 ≤ (bitSize u + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : 2 ^ (2 * bitSize u + 10) * 8 = 2 ^ (2 * bitSize u + 13) := by
      rw [show 2 * bitSize u + 13 = (2 * bitSize u + 10) + 3 by omega, pow_add 2 (2 * bitSize u + 10) 3]
      norm_num
    have h3 : 2 ^ (2 * bitSize u + 13) ≤ 2 ^ (20001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bndCW]
    generalize (u.length + mx u + 8) ^ 2 = b at h
    apply max_le <;> omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    have h3 : (u.length + 1) ^ 3 ≤ (bitSize u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h4 : 1 ≤ (bitSize u + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    simp only [Layout.const, cost]
    omega
  · have h1 := hmWord_lt u v hv
    have h := sq_fit8 u 0 (by norm_num)
    have hb3 : bitSize u + 1 ≤ (bitSize u + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : 2 ^ (2 * bitSize u + 10) ≤ 2 ^ (20001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold bndCW at h1
    omega

end Lax434175Proofs.HighMultiplicityProgram