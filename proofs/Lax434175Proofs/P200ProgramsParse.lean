import Mathlib.Tactic
import Lax434175Proofs.P200ProgramsSpec
import Lax434175Proofs.IsemPrograms

/-!
Reading the standard word (`parseWord`) as a word RAM program in IMP+, proved polynomial on
every word. The records are walked with a pointer `q` to the length of the current record.
-/

namespace Lax434175Proofs.P200Programs
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost
open Lax434175Proofs.IsemPrograms (V incr prelude arrW run_prelude getD_le_max ev_rd minTo run_minTo
  bndCW)
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub)

/-- The largest entry. -/
local notation "mx" => Lax434175.Results.maxEntry

-- The program

/-- `q := q + 1 + a[q]`: on to the next record. -/
def stepQ : Com := .seq (rdG "a" "L" "v" (V "q")) (.assign "q" (.add (.add (V "q") (.lit 1)) (V "v")))

/-- `b := 1` if job `j` has no machine. -/
def chkBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (V "q") (V "m")) (.lit 3))) <|
  .seq (.ite (.eq (V "v") (.lit 0)) (.assign "b" (.lit 1)) .skip) <|
  .seq stepQ (incr "j")

/-- `s += w_j` -/
def totBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (V "Q") (.mul (.lit 3) (V "j"))) (.lit 1))) <|
  .seq (.assign "s" (.add (V "s") (V "v"))) (incr "j")

/-- `write p_j` -/
def pBody : Com :=
  .seq (rdG "a" "L" "v" (.add (V "q") (.lit 2))) <| .seq (.write (V "v")) <| .seq stepQ (incr "j")

/-- `write` entry `r` of the objective triple of job `j` -/
def objBody (r : ℕ) : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (V "Q") (.mul (.lit 3) (V "j"))) (.lit r))) <|
  .seq (.write (V "v")) (incr "j")

/-- `s += c_j; write s` -/
def offBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (V "q") (V "m")) (.lit 3))) <| .seq (minTo "c" "v" "L") <|
  .seq (.assign "s" (.add (V "s") (V "c"))) <| .seq (.write (V "s")) <| .seq stepQ (incr "j")

/-- `write` the `t`-th machine of job `j` -/
def mchBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (.add (V "q") (V "m")) (.lit 6)) (.mul (.lit 3) (V "t")))) <|
  .seq (.write (V "v")) (incr "t")

/-- `write` the machines of job `j` -/
def tgBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (V "q") (V "m")) (.lit 3))) <| .seq (minTo "c" "v" "L") <|
  .seq (forLoop "t" "c" mchBody) <| .seq stepQ (incr "j")

/-- The word of an instance whose jobs all have a machine. -/
def goodCom : Com :=
  .seq (.assign "s" (.lit 0)) <| .seq (forLoop "j" "n" totBody) <|
  .seq (rdG "a" "L" "g" (.sub (V "L") (.lit 2))) <|
  .seq (rdG "a" "L" "h" (.sub (V "L") (.lit 1))) <|
  .seq (.ite (.eq (V "g") (.lit 0)) (.assign "W" (.sub (V "s") (V "h")))
    (.assign "W" (.add (V "s") (V "h")))) <|
  .seq (.seq (.write (V "n")) (.seq (.write (V "m")) (.write (V "W")))) <|
  .seq (.assign "q" (.lit 3)) <| .seq (forLoop "j" "n" pBody) <|
  .seq (forLoop "j" "n" (objBody 2)) <|
  .seq (forLoop "j" "n" (objBody 1)) <|
  .seq (.assign "s" (.lit 0)) <| .seq (.write (V "s")) <|
  .seq (.assign "q" (.lit 3)) <| .seq (forLoop "j" "n" offBody) <|
  .seq (.assign "q" (.lit 3)) (forLoop "j" "n" tgBody)

def pwCom : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 1)) <| .seq (minTo "n" "c" "L") <|
  .seq (rdG "a" "L" "m" (.lit 2)) <|
  .seq (.assign "b" (.lit 0)) <| .seq (.assign "q" (.lit 3)) <|
  .seq (forLoop "j" "n" chkBody) <|
  .seq (.assign "Q" (.add (V "q") (.lit 7))) <|
  .ite (.eq (V "b") (.lit 1)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 1)))) goodCom

def pwLayout : Layout :=
  ⟨["L", "i", "v", "c", "n", "m", "b", "q", "j", "Q", "s", "g", "h", "W", "t"], ["a"], 6⟩

theorem pwCom_ok : Com.Ok pwLayout pwCom := by
  simp [pwCom, goodCom, prelude, minTo, stepQ, chkBody, totBody, pBody, objBody, offBody, mchBody, tgBody,
    rdG, Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, pwLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

-- Bounds

theorem posA_le (u : List ℕ) (k : ℕ) : posA u k ≤ 3 + k * (mx u + 1) := by
  induction k with
  | zero => simp [posA]
  | succ k ih => rw [posA, Nat.succ_mul]; have := getD_le_max u (posA u k); omega

theorem nA_le (u : List ℕ) : nA u ≤ u.length := min_le_right _ _

theorem posA_le' {u : List ℕ} {k : ℕ} (hk : k ≤ nA u) : posA u k ≤ 3 + u.length * (mx u + 1) := by
  have := Nat.mul_le_mul_right (mx u + 1) (hk.trans (nA_le u))
  have := posA_le u k
  omega

/-- What the value bound must admit. -/
structure Bnd (u : List ℕ) (B : ℕ) : Prop where
  idx : 3 + u.length * (mx u + 1) + mx u + 3 * u.length + 20 < B
  sum : u.length * mx u + mx u + u.length * u.length + u.length + 10 < B

theorem bnd_of {u : List ℕ} {B : ℕ} (hB : 8 * (u.length + mx u + 8) ^ 2 ≤ B) : Bnd u B :=
  ⟨by nlinarith, by nlinarith⟩

theorem Bnd.M {u : List ℕ} {B : ℕ} (b : Bnd u B) : mx u < B := by have := b.idx; omega
theorem Bnd.Lt {u : List ℕ} {B : ℕ} (b : Bnd u B) : u.length < B := by have := b.idx; omega
theorem Bnd.pos {u : List ℕ} {B : ℕ} (b : Bnd u B) {k : ℕ} (hk : k ≤ nA u) (c : ℕ)
    (hc : c ≤ mx u + 3 * u.length + 20) : posA u k + c < B := by
  have := posA_le' hk; have := b.idx; omega

section PW
variable {B : ℕ} {u : List ℕ} {Qv : ℕ}

/-- What stays fixed while parsing. -/
structure PC (u : List ℕ) (Qv : ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = arrW u
  L : τ.vars "L" = u.length
  n : τ.vars "n" = nA u
  m : τ.vars "m" = mA u
  Q : τ.vars "Q" = Qv

theorem PC.setVar {τ : Env} (h : PC u Qv τ) {y : String} (h1 : y ≠ "L") (h2 : y ≠ "n") (h3 : y ≠ "m")
    (h4 : y ≠ "Q") (w : ℕ) : PC u Qv (τ.setVar y w) :=
  ⟨by simp [h.a], by simp [h1.symm, h.L], by simp [h2.symm, h.n], by simp [h3.symm, h.m],
    by simp [h4.symm, h.Q]⟩

theorem PC.out {τ : Env} (h : PC u Qv τ) (o : List ℕ) : PC u Qv { τ with out := o } :=
  ⟨h.a, h.L, h.n, h.m, h.Q⟩

theorem posA_succ (u : List ℕ) (k : ℕ) : posA u (k + 1) = posA u k + 1 + u.getD (posA u k) 0 := rfl

theorem run_stepQ (bd : Bnd u B) {τ : Env} (h : PC u Qv τ) {k : ℕ} (hk : k < nA u)
    (hq : τ.vars "q" = posA u k) :
    Run B stepQ τ ((τ.setVar "v" (u.getD (posA u k) 0)).setVar "q" (posA u (k + 1))) 13 := by
  have hp := bd.pos (k := k + 1) hk 0 (by omega)
  have r1 := ev_rd h.a h.L (e := V "q") (ev_var hq (bd.pos hk.le 0 (by omega))) bd.M bd.Lt "v"
  have hv := getD_le_max u (posA u k)
  rw [posA_succ] at hp ⊢
  exact (r1.seq (Run.assign (ev_add (ev_add (ev_var (by simp [hq]) (by omega)) (ev_lit (by omega))
    (by omega)) (ev_var (by simp) (by omega)) (by omega)))).mono (by simp)

/-- The `j`-th read of the loop variable. -/
theorem ev_jv {τ : Env} {k : ℕ} (hj : τ.vars "j" = k) (hk : k < B) : (V "j").evalB B τ = some k :=
  ev_var hj hk

theorem run_incr {τ : Env} (x : String) {k : ℕ} (hx : τ.vars x = k) (hk : k + 1 < B) :
    Run B (incr x) τ (τ.setVar x (k + 1)) 4 :=
  (Run.assign (ev_add (ev_var hx (by omega)) (ev_lit (by omega)) hk)).mono (by simp)

/-- **The check that every job has a machine.** -/
theorem run_chk (bd : Bnd u B) {τ : Env} (h : PC u Qv τ) (hq : τ.vars "q" = 3) (hb : τ.vars "b" = 0) :
    ∃ τ', Run B (forLoop "j" "n" chkBody) τ τ' (44 * nA u + 6) ∧ PC u Qv τ' ∧
      τ'.vars "q" = posA u (nA u) ∧ τ'.vars "b" = (if badA u then 1 else 0) ∧ τ'.out = τ.out := by
  have hn := nA_le u
  obtain ⟨τ', hr, -, hc, hq', hb', ho⟩ := run_forLoop (B := B) "j" "n" chkBody (nA u) 40 (by
      have := bd.Lt; omega)
    (fun k σ => σ.vars "j" = k ∧ PC u Qv σ ∧ σ.vars "q" = posA u k ∧
      σ.vars "b" = (if (List.range k).any (fun j => cntA u j == 0) then 1 else 0) ∧ σ.out = τ.out)
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, hqk, hbk, ho⟩ => by
      have hP := bd.pos hk.le (mx u + 3 * u.length + 20) le_rfl
      have hmA : mA u ≤ mx u := getD_le_max u 2
      have i1 : (Expr.add (.add (V "q") (V "m")) (.lit 3)).evalB B σ = some (posA u k + mA u + 3) :=
        ev_add (ev_add (ev_var hqk (by omega)) (ev_var hc.m (by omega)) (by omega))
          (ev_lit (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L i1 bd.M bd.Lt "v"
      rw [show u.getD (posA u k + mA u + 3) 0 = cntA u k from rfl] at r1
      set σ1 := σ.setVar "v" (cntA u k)
      have hc1 : PC u Qv σ1 := hc.setVar (by decide) (by decide) (by decide) (by decide) _
      have hany : (List.range (k + 1)).any (fun j => cntA u j == 0) =
          ((List.range k).any (fun j => cntA u j == 0) || (cntA u k == 0)) := by
        rw [List.range_succ, List.any_append]; simp
      have hcond : (Cond.eq (V "v") (.lit 0)).evalB B σ1 = some (cntA u k == 0) :=
        evalB_condEq (ev_var (by simp [σ1]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
          (ev_lit (by have := bd.Lt; omega))
      have hfin : ∀ σ2 : Env, PC u Qv σ2 → σ2.vars "q" = posA u k → σ2.vars "j" = k →
          ∃ σ3, Run B (.seq stepQ (incr "j")) σ2 σ3 17 ∧ σ3.vars "j" = k + 1 ∧ PC u Qv σ3 ∧
            σ3.vars "q" = posA u (k + 1) ∧ σ3.vars "b" = σ2.vars "b" ∧ σ3.out = σ2.out := by
        intro σ2 hc2 hq2 hj2
        exact ⟨_, (run_stepQ bd hc2 hk hq2).seq (run_incr (k := k) "j" (by simp [hj2]) (by have := bd.Lt; omega)),
          by simp, ((hc2.setVar (by decide) (by decide) (by decide) (by decide) _).setVar (by decide)
            (by decide) (by decide) (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _,
          by simp, by simp, by simp⟩
      by_cases h0 : cntA u k = 0
      · obtain ⟨σ3, r3, hj3, hc3, hq3, hb3, ho3⟩ := hfin (σ1.setVar "b" 1)
          (hc1.setVar (by decide) (by decide) (by decide) (by decide) _) (by simp [σ1, hqk])
          (by simp [σ1, hj])
        refine ⟨σ3, (r1.seq ((Run.ite_true (by rw [hcond]; simp [h0]) (Run.assign (ev_lit (by
          have := bd.Lt; omega)))).seq r3)).mono (by simp), hj3, hc3, hq3, ?_, by rw [ho3]; simp [σ1, ho]⟩
        rw [hb3, hany]; simp [h0]
      · obtain ⟨σ3, r3, hj3, hc3, hq3, hb3, ho3⟩ := hfin σ1 hc1 (by simp [σ1, hqk]) (by simp [σ1, hj])
        refine ⟨σ3, (r1.seq ((Run.ite_false (by rw [hcond]; simp [h0]) Run.skip).seq r3)).mono (by simp),
          hj3, hc3, hq3, ?_, by rw [ho3]; simp [σ1, ho]⟩
        rw [hb3, hany]; simp [σ1, hbk, h0])
    (σ := τ) ⟨by simp, h.setVar (by decide) (by decide) (by decide) (by decide) _, by simp [hq]; rfl,
      by simp [hb], by simp⟩
  exact ⟨τ', hr.mono (by omega), hc, hq', by rw [hb']; rfl, ho⟩

theorem PC.ofVars {τ τ' : Env} (h : PC u Qv τ) (ha : τ'.arrs = τ.arrs)
    (hv : ∀ y, y = "L" ∨ y = "n" ∨ y = "m" ∨ y = "Q" → τ'.vars y = τ.vars y) : PC u Qv τ' :=
  ⟨by rw [ha, h.a], by rw [hv _ (by simp), h.L], by rw [hv _ (by simp), h.n], by rw [hv _ (by simp), h.m],
    by rw [hv _ (by simp), h.Q]⟩

theorem objA_bound (bd : Bnd u B) (c : ℕ) (hc : c ≤ 3 * u.length + 10) : objA u + c < B := by
  have := bd.pos (le_refl (nA u)) (c + 7) (by omega)
  unfold objA; omega

theorem wA_le (u : List ℕ) (j : ℕ) : wA u j ≤ mx u := getD_le_max u _

theorem totA_le (u : List ℕ) (k : ℕ) : psum (wA u) k ≤ k * mx u := psum_le_mul _ (wA_le u) k

/-- **The total weight.** -/
theorem run_tot (bd : Bnd u B) (hQ : Qv = objA u) {τ : Env} (h : PC u Qv τ) (hs : τ.vars "s" = 0) :
    ∃ τ', Run B (forLoop "j" "n" totBody) τ τ' (31 * nA u + 6) ∧ PC u Qv τ' ∧
      τ'.vars "s" = totA u ∧ τ'.out = τ.out := by
  have hn := nA_le u
  obtain ⟨τ', hr, -, hc, hs', ho⟩ := run_forLoop (B := B) "j" "n" totBody (nA u) 27 (by
      have := bd.Lt; omega)
    (fun k σ => σ.vars "j" = k ∧ PC u Qv σ ∧ σ.vars "s" = psum (wA u) k ∧ σ.out = τ.out)
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, hsk, ho⟩ => by
      have hO := objA_bound bd (3 * k + 1) (by omega)
      have hB20 := bd.idx
      have i1 : (Expr.add (.add (V "Q") (.mul (.lit 3) (V "j"))) (.lit 1)).evalB B σ =
          some (objA u + 3 * k + 1) := by
        exact ev_add (ev_add (ev_var (hc.Q.trans hQ) (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hj (by omega))
          (by omega)) (by omega)) (ev_lit (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L i1 bd.M bd.Lt "v"
      rw [show u.getD (objA u + 3 * k + 1) 0 = wA u k from rfl] at r1
      have h1 := totA_le u k
      have h2 := wA_le u k
      have h3 : k * mx u + mx u ≤ u.length * mx u := by
        have := Nat.mul_le_mul_right (mx u) (show k + 1 ≤ u.length by omega); rw [Nat.succ_mul] at this; exact this
      have hsum := bd.sum
      have r2 : Run B (.assign "s" (.add (V "s") (V "v"))) (σ.setVar "v" (wA u k))
          ((σ.setVar "v" (wA u k)).setVar "s" (psum (wA u) k + wA u k)) 4 :=
        (Run.assign (ev_add (ev_var (by simp [hsk]) (by omega)) (ev_var (by simp) (by omega)) (by omega))).mono
          (by simp)
      refine ⟨_, (r1.seq (r2.seq (run_incr (k := k) "j" (by simp [hj]) (by omega)))).mono (by simp),
        by simp, ((hc.setVar (by decide) (by decide) (by decide) (by decide) _).setVar (by decide) (by decide)
          (by decide) (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _,
        by simp [psum_succ], by simp [ho]⟩)
    (σ := τ) ⟨by simp, h.setVar (by decide) (by decide) (by decide) (by decide) _, by simp [hs], by simp⟩
  exact ⟨τ', hr, hc, hs', ho⟩

/-- **The processing times.** -/
theorem run_p (bd : Bnd u B) {τ : Env} (h : PC u Qv τ) (hq : τ.vars "q" = 3) :
    ∃ τ', Run B (forLoop "j" "n" pBody) τ τ' (34 * nA u + 6) ∧ PC u Qv τ' ∧
      τ'.out = τ.out ++ (List.range (nA u)).map (pA u) := by
  have hn := nA_le u
  obtain ⟨τ', hr, -, hc, -, ho⟩ := run_forLoop (B := B) "j" "n" pBody (nA u) 30 (by
      have := bd.Lt; omega)
    (fun k σ => σ.vars "j" = k ∧ PC u Qv σ ∧ σ.vars "q" = posA u k ∧
      σ.out = τ.out ++ (List.range k).map (pA u))
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, hqk, ho⟩ => by
      have hP := bd.pos hk.le (mx u + 3 * u.length + 20) le_rfl
      have r1 := ev_rd hc.a hc.L (e := .add (V "q") (.lit 2))
        (ev_add (ev_var hqk (by omega)) (ev_lit (by omega)) (by omega)) bd.M bd.Lt "v"
      rw [show u.getD (posA u k + 2) 0 = pA u k from rfl] at r1
      set σ1 := σ.setVar "v" (pA u k)
      have r2 : Run B (.write (V "v")) σ1 { σ1 with out := σ1.out ++ [pA u k] } 2 :=
        Run.write (ev_var (by simp [σ1]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
      set σ2 : Env := { σ1 with out := σ1.out ++ [pA u k] }
      have hc2 : PC u Qv σ2 := (hc.setVar (by decide) (by decide) (by decide) (by decide) _).out _
      have r3 := run_stepQ bd hc2 hk (by simp [σ2, σ1, hqk])
      refine ⟨_, (r1.seq (r2.seq (r3.seq (run_incr (k := k) "j" (by simp [σ2, σ1, hj])
        (by have := bd.Lt; omega))))).mono (by simp), by simp,
        ((hc2.setVar (by decide) (by decide) (by decide) (by decide) _).setVar (by decide) (by decide)
          (by decide) (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _,
        by simp, ?_⟩
      simp [σ2, σ1, ho, List.range_succ])
    (σ := τ) ⟨by simp, h.setVar (by decide) (by decide) (by decide) (by decide) _, by simp [hq]; rfl, by simp⟩
  exact ⟨τ', hr, hc, ho⟩

/-- **Entry `r` of the objective triples.** -/
theorem run_obj (bd : Bnd u B) (hQ : Qv = objA u) (r : ℕ) (hr : r ≤ 2) {τ : Env} (h : PC u Qv τ) :
    ∃ τ', Run B (forLoop "j" "n" (objBody r)) τ τ' (29 * nA u + 6) ∧ PC u Qv τ' ∧
      τ'.out = τ.out ++ (List.range (nA u)).map (fun j => u.getD (objA u + 3 * j + r) 0) := by
  have hn := nA_le u
  obtain ⟨τ', hr', -, hc, ho⟩ := run_forLoop (B := B) "j" "n" (objBody r) (nA u) 25 (by
      have := bd.Lt; omega)
    (fun k σ => σ.vars "j" = k ∧ PC u Qv σ ∧
      σ.out = τ.out ++ (List.range k).map (fun j => u.getD (objA u + 3 * j + r) 0))
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, ho⟩ => by
      have hO := objA_bound bd (3 * k + r) (by omega)
      have hB20 := bd.idx
      have i1 : (Expr.add (.add (V "Q") (.mul (.lit 3) (V "j"))) (.lit r)).evalB B σ =
          some (objA u + 3 * k + r) := by
        exact ev_add (ev_add (ev_var (hc.Q.trans hQ) (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hj (by omega))
          (by omega)) (by omega)) (ev_lit (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L i1 bd.M bd.Lt "v"
      set σ1 := σ.setVar "v" (u.getD (objA u + 3 * k + r) 0)
      have r2 : Run B (.write (V "v")) σ1 { σ1 with out := σ1.out ++ [u.getD (objA u + 3 * k + r) 0] } 2 :=
        Run.write (ev_var (by simp [σ1]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
      have hc2 := (hc.setVar (y := "v") (by decide) (by decide) (by decide) (by decide)
        (u.getD (objA u + 3 * k + r) 0)).out (σ1.out ++ [u.getD (objA u + 3 * k + r) 0])
      refine ⟨_, (r1.seq (r2.seq (run_incr (k := k) "j" (by simp [σ1, hj])
        (by have := bd.Lt; omega)))).mono (by simp), by simp,
        hc2.setVar (by decide) (by decide) (by decide) (by decide) _, ?_⟩
      simp [σ1, ho, List.range_succ])
    (σ := τ) ⟨by simp, h.setVar (by decide) (by decide) (by decide) (by decide) _, by simp⟩
  exact ⟨τ', hr', hc, ho⟩

theorem cA_le (u : List ℕ) (j : ℕ) : cA u j ≤ u.length := min_le_right _ _

theorem offA_le (u : List ℕ) (k : ℕ) : offA u k ≤ k * u.length := psum_le_mul _ (cA_le u) k

/-- **The offsets.** -/
theorem run_off (bd : Bnd u B) {τ : Env} (h : PC u Qv τ) (hq : τ.vars "q" = 3) (hs : τ.vars "s" = 0) :
    ∃ τ', Run B (forLoop "j" "n" offBody) τ τ' (48 * nA u + 6) ∧ PC u Qv τ' ∧
      τ'.out = τ.out ++ (List.range (nA u)).map (fun j => offA u (j + 1)) := by
  have hn := nA_le u
  obtain ⟨τ', hr, -, hc, -, -, ho⟩ := run_forLoop (B := B) "j" "n" offBody (nA u) 44 (by
      have := bd.Lt; omega)
    (fun k σ => σ.vars "j" = k ∧ PC u Qv σ ∧ σ.vars "q" = posA u k ∧ σ.vars "s" = offA u k ∧
      σ.out = τ.out ++ (List.range k).map (fun j => offA u (j + 1)))
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, hqk, hsk, ho⟩ => by
      have hP := bd.pos hk.le (mx u + 3 * u.length + 20) le_rfl
      have hmA : mA u ≤ mx u := getD_le_max u 2
      have i1 : (Expr.add (.add (V "q") (V "m")) (.lit 3)).evalB B σ = some (posA u k + mA u + 3) :=
        ev_add (ev_add (ev_var hqk (by omega)) (ev_var hc.m (by omega)) (by omega))
          (ev_lit (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L i1 bd.M bd.Lt "v"
      rw [show u.getD (posA u k + mA u + 3) 0 = cntA u k from rfl] at r1
      set σ1 := σ.setVar "v" (cntA u k)
      have r2 : Run B (minTo "c" "v" "L") σ1 (σ1.setVar "c" (cA u k)) 6 :=
        run_minTo (by simp [σ1]) (by simp [σ1, hc.L]) (lt_of_le_of_lt (getD_le_max u _) bd.M) bd.Lt
      set σ2 := σ1.setVar "c" (cA u k)
      have h1 := offA_le u k
      have h2 := cA_le u k
      have h3 : k * u.length + u.length ≤ u.length * u.length := by
        have := Nat.mul_le_mul_right u.length (show k + 1 ≤ u.length by omega); rw [Nat.succ_mul] at this
        exact this
      have hsum := bd.sum
      have hoff : offA u (k + 1) = offA u k + cA u k := psum_succ _ _
      have r3 : Run B (.assign "s" (.add (V "s") (V "c"))) σ2 (σ2.setVar "s" (offA u (k + 1))) 4 := by
        rw [hoff]
        exact (Run.assign (ev_add (ev_var (by simp [σ2, σ1, hsk]) (by omega)) (ev_var (by simp [σ2]) (by omega))
          (by omega))).mono (by simp)
      set σ3 := σ2.setVar "s" (offA u (k + 1))
      have r4 : Run B (.write (V "s")) σ3 { σ3 with out := σ3.out ++ [offA u (k + 1)] } 2 :=
        Run.write (ev_var (by simp [σ3]) (by omega))
      set σ4 : Env := { σ3 with out := σ3.out ++ [offA u (k + 1)] }
      have hc4 : PC u Qv σ4 := (((hc.setVar (by decide) (by decide) (by decide) (by decide) _).setVar
        (by decide) (by decide) (by decide) (by decide) _).setVar (by decide) (by decide) (by decide)
        (by decide) _).out _
      have r5 := run_stepQ bd hc4 hk (by simp [σ4, σ3, σ2, σ1, hqk])
      refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (run_incr (k := k) "j"
        (by simp [σ4, σ3, σ2, σ1, hj]) (by have := bd.Lt; omega))))))).mono (by simp), by simp,
        ((hc4.setVar (by decide) (by decide) (by decide) (by decide) _).setVar (by decide) (by decide)
          (by decide) (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _,
        by simp, by simp [σ4, σ3], ?_⟩
      simp [σ4, σ3, σ2, σ1, ho, List.range_succ])
    (σ := τ) ⟨by simp, h.setVar (by decide) (by decide) (by decide) (by decide) _, by simp [hq]; rfl,
      by simp [hs]; rfl, by simp⟩
  exact ⟨τ', hr, hc, ho⟩

/-- **The machines of one job.** -/
theorem run_mch (bd : Bnd u B) {τ : Env} (h : PC u Qv τ) {k : ℕ} (hk : k < nA u)
    (hq : τ.vars "q" = posA u k) (hcv : τ.vars "c" = cA u k) :
    ∃ τ', Run B (forLoop "t" "c" mchBody) τ τ' (33 * cA u k + 6) ∧
      τ'.out = τ.out ++ (List.range (cA u k)).map (mchA u k) ∧ τ'.arrs = τ.arrs ∧
      (∀ y, y ≠ "t" → y ≠ "v" → τ'.vars y = τ.vars y) := by
  have hP := bd.pos hk.le (mx u + 3 * u.length + 20) le_rfl
  have hmA : mA u ≤ mx u := getD_le_max u 2
  have hcL := cA_le u k
  obtain ⟨τ', hr, -, ho, ha, hfr⟩ := run_forLoop (B := B) "t" "c" mchBody (cA u k) 29 (by
      have := bd.Lt; omega)
    (fun i σ => σ.vars "t" = i ∧ σ.out = τ.out ++ (List.range i).map (mchA u k) ∧ σ.arrs = τ.arrs ∧
      (∀ y, y ≠ "t" → y ≠ "v" → σ.vars y = τ.vars y))
    (fun i σ h => h.1) (fun i σ h => by rw [h.2.2.2 "c" (by decide) (by decide), hcv])
    (fun i hi σ ⟨ht, hoo, haa, hfr⟩ => by
      have hc : PC u Qv σ := h.ofVars haa (fun y hy => by
        rcases hy with rfl | rfl | rfl | rfl <;> exact hfr _ (by decide) (by decide))
      have hqq : σ.vars "q" = posA u k := by rw [hfr "q" (by decide) (by decide), hq]
      have i1 : (Expr.add (.add (.add (V "q") (V "m")) (.lit 6)) (.mul (.lit 3) (V "t"))).evalB B σ =
          some (posA u k + mA u + 6 + 3 * i) :=
        ev_add (ev_add (ev_add (ev_var hqq (by omega)) (ev_var hc.m (by omega)) (by omega)) (ev_lit (by omega))
          (by omega)) (ev_mul (ev_lit (by omega)) (ev_var ht (by omega)) (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L i1 bd.M bd.Lt "v"
      rw [show u.getD (posA u k + mA u + 6 + 3 * i) 0 = mchA u k i from rfl] at r1
      set σ1 := σ.setVar "v" (mchA u k i)
      have r2 : Run B (.write (V "v")) σ1 { σ1 with out := σ1.out ++ [mchA u k i] } 2 :=
        Run.write (ev_var (by simp [σ1]) (lt_of_le_of_lt (getD_le_max u _) bd.M))
      refine ⟨_, (r1.seq (r2.seq (run_incr (k := i) "t" (by simp [σ1, ht]) (by have := bd.Lt; omega)))).mono
        (by simp), by simp, by simp [σ1, hoo, List.range_succ], by simp [σ1, haa],
        fun y h1 h2 => by simp [σ1, h1, h2, hfr y h1 h2]⟩)
    (σ := τ) ⟨by simp, by simp, by simp, fun y h1 _ => by simp [h1]⟩
  exact ⟨τ', hr, ho, ha, hfr⟩

/-- **The machines of all jobs.** -/
theorem run_tg (bd : Bnd u B) {τ : Env} (h : PC u Qv τ) (hq : τ.vars "q" = 3) :
    ∃ τ', Run B (forLoop "j" "n" tgBody) τ τ' ((33 * u.length + 48) * nA u + 6) ∧
      τ'.out = τ.out ++ (List.range (nA u)).flatMap (fun j => (List.range (cA u j)).map (mchA u j)) := by
  have hn := nA_le u
  obtain ⟨τ', hr, -, -, -, ho⟩ := run_forLoop (B := B) "j" "n" tgBody (nA u) (33 * u.length + 44) (by
      have := bd.Lt; omega)
    (fun k σ => σ.vars "j" = k ∧ PC u Qv σ ∧ σ.vars "q" = posA u k ∧
      σ.out = τ.out ++ (List.range k).flatMap (fun j => (List.range (cA u j)).map (mchA u j)))
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, hqk, ho⟩ => by
      have hP := bd.pos hk.le (mx u + 3 * u.length + 20) le_rfl
      have hmA : mA u ≤ mx u := getD_le_max u 2
      have i1 : (Expr.add (.add (V "q") (V "m")) (.lit 3)).evalB B σ = some (posA u k + mA u + 3) :=
        ev_add (ev_add (ev_var hqk (by omega)) (ev_var hc.m (by omega)) (by omega))
          (ev_lit (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L i1 bd.M bd.Lt "v"
      rw [show u.getD (posA u k + mA u + 3) 0 = cntA u k from rfl] at r1
      set σ1 := σ.setVar "v" (cntA u k)
      have r2 : Run B (minTo "c" "v" "L") σ1 (σ1.setVar "c" (cA u k)) 6 :=
        run_minTo (by simp [σ1]) (by simp [σ1, hc.L]) (lt_of_le_of_lt (getD_le_max u _) bd.M) bd.Lt
      set σ2 := σ1.setVar "c" (cA u k)
      have hc2 : PC u Qv σ2 := (hc.setVar (by decide) (by decide) (by decide) (by decide) _).setVar
        (by decide) (by decide) (by decide) (by decide) _
      obtain ⟨σ3, r3, ho3, ha3, hfr3⟩ := run_mch bd hc2 hk (by simp [σ2, σ1, hqk]) (by simp [σ2])
      have hc3 : PC u Qv σ3 := hc2.ofVars ha3 (fun y hy => by
        rcases hy with rfl | rfl | rfl | rfl <;> exact hfr3 _ (by decide) (by decide))
      have r4 := run_stepQ bd hc3 hk (by rw [hfr3 "q" (by decide) (by decide)]; simp [σ2, σ1, hqk])
      have hj3 : σ3.vars "j" = k := by rw [hfr3 "j" (by decide) (by decide)]; simp [σ2, σ1, hj]
      have hcL := cA_le u k
      refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (run_incr (k := k) "j" (by simp [hj3])
        (by have := bd.Lt; omega)))))).mono (by simp; nlinarith), by simp,
        ((hc3.setVar (by decide) (by decide) (by decide) (by decide) _).setVar (by decide) (by decide)
          (by decide) (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _,
        by simp, ?_⟩
      simp [ho3, σ2, σ1, ho, List.range_succ])
    (σ := τ) ⟨by simp, h.setVar (by decide) (by decide) (by decide) (by decide) _, by simp [hq]; rfl, by simp⟩
  exact ⟨τ', hr, ho⟩

theorem WA_le (u : List ℕ) : WA u ≤ u.length * mx u + mx u := by
  have h1 := totA_le u (nA u)
  have h2 : nA u * mx u ≤ u.length * mx u := Nat.mul_le_mul_right _ (nA_le u)
  have h3 := getD_le_max u (u.length - 1)
  unfold WA totA at *
  split_ifs <;> omega

/-- **The word of an instance whose jobs all have a machine.** -/
theorem run_good (bd : Bnd u B) {τ : Env} (h : PC u (objA u) τ) :
    ∃ τ', Run B goodCom τ τ' ((33 * u.length + 300) * nA u + 200) ∧
      τ'.out = τ.out ++ ([nA u, mA u, WA u] ++ (List.range (nA u)).map (pA u) ++
        (List.range (nA u)).map (dA u) ++ (List.range (nA u)).map (wA u) ++
        ([0] ++ (List.range (nA u)).map (fun j => offA u (j + 1))) ++
        (List.range (nA u)).flatMap fun j => (List.range (cA u j)).map (mchA u j)) := by
  have hB20 := bd.idx
  have hsum := bd.sum
  have hn := nA_le u
  have hMB := bd.M
  set s0 := τ.setVar "s" 0
  have r0 : Run B (.assign "s" (.lit 0)) τ s0 2 := Run.assign (ev_lit (by omega))
  obtain ⟨s1, r1, hc1, hs1, ho1⟩ := run_tot bd rfl (h.setVar (y := "s") (by decide) (by decide) (by decide)
    (by decide) 0) (by simp)
  have r2 := ev_rd hc1.a hc1.L (e := .sub (V "L") (.lit 2)) (ev_sub (ev_var hc1.L bd.Lt) (ev_lit (by omega)))
    bd.M bd.Lt "g"
  set gv := u.getD (u.length - 2) 0
  set s2 := s1.setVar "g" gv
  have hc2 : PC u (objA u) s2 := hc1.setVar (by decide) (by decide) (by decide) (by decide) _
  have r3 := ev_rd hc2.a hc2.L (e := .sub (V "L") (.lit 1)) (ev_sub (ev_var hc2.L bd.Lt) (ev_lit (by omega)))
    bd.M bd.Lt "h"
  set hv := u.getD (u.length - 1) 0
  set s3 := s2.setVar "h" hv
  have hc3 : PC u (objA u) s3 := hc2.setVar (by decide) (by decide) (by decide) (by decide) _
  have hts := totA_le u (nA u)
  have htl : nA u * mx u ≤ u.length * mx u := Nat.mul_le_mul_right _ hn
  have hhv : hv ≤ mx u := getD_le_max u _
  have hts' : totA u ≤ u.length * mx u := hts.trans htl
  have hs3 : s3.vars "s" = totA u := by simp [s3, s2, hs1]
  have hh3 : s3.vars "h" = hv := by simp [s3]
  have hcond : (Cond.eq (V "g") (.lit 0)).evalB B s3 = some (gv == 0) :=
    evalB_condEq (ev_var (by simp [s3, s2]) (lt_of_le_of_lt (getD_le_max u _) bd.M)) (ev_lit (by omega))
  have r4 : Run B (.ite (.eq (V "g") (.lit 0)) (.assign "W" (.sub (V "s") (V "h")))
      (.assign "W" (.add (V "s") (V "h")))) s3 (s3.setVar "W" (WA u)) 8 := by
    by_cases hg : gv = 0
    · have e : WA u = totA u - hv := by unfold WA; rw [if_pos hg]
      rw [e]
      exact (Run.ite_true (by rw [hcond]; simp [hg]) (Run.assign (ev_sub (ev_var hs3 (by omega))
        (ev_var hh3 (by omega))))).mono (by simp)
    · have e : WA u = totA u + hv := by unfold WA; rw [if_neg hg]
      rw [e]
      exact (Run.ite_false (by rw [hcond]; simp [hg]) (Run.assign (ev_add (ev_var hs3 (by omega))
        (ev_var hh3 (by omega)) (by omega)))).mono (by simp)
  set s4 := s3.setVar "W" (WA u)
  have hc4 : PC u (objA u) s4 := hc3.setVar (by decide) (by decide) (by decide) (by decide) _
  have hWl := WA_le u
  have hmA : mA u ≤ mx u := getD_le_max u 2
  have r5 : Run B (.seq (.write (V "n")) (.seq (.write (V "m")) (.write (V "W")))) s4
      { s4 with out := s4.out ++ [nA u] ++ [mA u] ++ [WA u] } 6 :=
    (Run.write (ev_var hc4.n (by omega))).seq ((Run.write (ev_var (σ := { s4 with out := s4.out ++ [nA u] })
      hc4.m (by omega))).seq (Run.write (ev_var (σ := { s4 with out := s4.out ++ [nA u] ++ [mA u] })
      (show s4.vars "W" = WA u by simp [s4]) (by omega))))
  set s5 : Env := { s4 with out := s4.out ++ [nA u] ++ [mA u] ++ [WA u] }
  have r6 : Run B (.assign "q" (.lit 3)) s5 (s5.setVar "q" 3) 2 := Run.assign (ev_lit (by omega))
  obtain ⟨s7, r7, hc7, ho7⟩ := run_p bd ((hc4.out _).setVar (y := "q") (by decide) (by decide) (by decide)
    (by decide) 3) (by simp)
  obtain ⟨s8, r8, hc8, ho8⟩ := run_obj bd rfl 2 (by norm_num) hc7
  obtain ⟨s9, r9, hc9, ho9⟩ := run_obj bd rfl 1 (by norm_num) hc8
  have r10 : Run B (.assign "s" (.lit 0)) s9 (s9.setVar "s" 0) 2 := Run.assign (ev_lit (by omega))
  set s10 := s9.setVar "s" 0
  have r11 : Run B (.write (V "s")) s10 { s10 with out := s10.out ++ [0] } 2 :=
    Run.write (ev_var (by simp [s10]) (by omega))
  set s11 : Env := { s10 with out := s10.out ++ [0] }
  have r12 : Run B (.assign "q" (.lit 3)) s11 (s11.setVar "q" 3) 2 := Run.assign (ev_lit (by omega))
  have hc12 : PC u (objA u) (s11.setVar "q" 3) :=
    (((hc9.setVar (y := "s") (by decide) (by decide) (by decide) (by decide) 0).out _).setVar (y := "q")
      (by decide) (by decide) (by decide) (by decide) 3)
  obtain ⟨s13, r13, hc13, ho13⟩ := run_off bd hc12 (by simp) (by simp [s11, s10])
  have r14 : Run B (.assign "q" (.lit 3)) s13 (s13.setVar "q" 3) 2 := Run.assign (ev_lit (by omega))
  obtain ⟨s15, r15, ho15⟩ := run_tg bd (hc13.setVar (y := "q") (by decide) (by decide) (by decide)
    (by decide) 3) (by simp)
  refine ⟨_, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq (r13.seq (r14.seq r15))))))))))))))).mono ?_, ?_⟩
  · simp only [Expr.size]
    nlinarith
  · rw [ho15]
    simp only [out_setVar, ho13, s11, s10, ho9, ho8, ho7, s4, s3, s2, ho1]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- The value bound. -/
theorem run_pw (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndCW u) pwCom (initEnv ext (u.length :: u)) σ'
      (400 * (u.length + 1) ^ 2) ∧ σ'.out = parseWord u := by
  have hB0 : 8 * (u.length + mx u + 8) ^ 2 ≤ bndCW u := le_rfl
  have bd := bnd_of hB0
  set B := bndCW u
  have hB20 := bd.idx
  have hn := nA_le u
  obtain ⟨σ2, r1, ha, hL2, hout2, hz, -⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) bd.M) (by omega)
  refine ⟨fun _ => u.length + 2, ?_⟩
  have r2 := ev_rd ha hL2 (e := .lit 1) (evalB_lit (by omega)) bd.M bd.Lt "c"
  set s2 := σ2.setVar "c" (u.getD 1 0)
  have r3 : Run B (minTo "n" "c" "L") s2 (s2.setVar "n" (nA u)) 6 :=
    run_minTo (by simp [s2]) (by simp [s2, hL2]) (lt_of_le_of_lt (getD_le_max u _) bd.M) bd.Lt
  set s3 := s2.setVar "n" (nA u)
  have r4 := ev_rd (σ := s3) (by simp [s3, s2, ha]) (by simp [s3, s2, hL2]) (e := .lit 2)
    (evalB_lit (by omega)) bd.M bd.Lt "m"
  set s4 := s3.setVar "m" (mA u)
  have r5 : Run B (.assign "b" (.lit 0)) s4 (s4.setVar "b" 0) 2 := Run.assign (ev_lit (by omega))
  have r6 : Run B (.assign "q" (.lit 3)) (s4.setVar "b" 0) ((s4.setVar "b" 0).setVar "q" 3) 2 :=
    Run.assign (ev_lit (by omega))
  set s6 := (s4.setVar "b" 0).setVar "q" 3
  have hc6 : PC u 0 s6 :=
    ⟨by simp [s6, s4, s3, s2, ha], by simp [s6, s4, s3, s2, hL2], by simp [s6, s4, s3],
      by simp [s6, s4], by simp [s6, s4, s3, s2]; exact hz "Q" (by decide) (by decide) (by decide)⟩
  obtain ⟨s7, r7, hc7, hq7, hb7, ho7⟩ := run_chk bd hc6 (by simp [s6]) (by simp [s6])
  have hP := bd.pos (le_refl (nA u)) 7 (by omega)
  have r8 : Run B (.assign "Q" (.add (V "q") (.lit 7))) s7 (s7.setVar "Q" (objA u)) 4 :=
    (Run.assign (ev_add (ev_var hq7 (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
  set s8 := s7.setVar "Q" (objA u)
  have hc8 : PC u (objA u) s8 := ⟨by simp [s8, hc7.a], by simp [s8, hc7.L], by simp [s8, hc7.n],
    by simp [s8, hc7.m], by simp [s8]⟩
  have hcond : (Cond.eq (V "b") (.lit 1)).evalB B s8 = some ((if badA u then 1 else 0) == 1) :=
    evalB_condEq (ev_var (by simp [s8, hb7]) (by split_ifs <;> omega)) (ev_lit (by omega))
  have pre : ∀ {c : Com} {σ' : Env} {K : ℕ}, Run B c s8 σ' K → Run B (.seq prelude (.seq (rdG "a" "L" "c" (.lit 1))
      (.seq (minTo "n" "c" "L") (.seq (rdG "a" "L" "m" (.lit 2)) (.seq (.assign "b" (.lit 0))
      (.seq (.assign "q" (.lit 3)) (.seq (forLoop "j" "n" chkBody) (.seq (.assign "Q" (.add (V "q") (.lit 7)))
      c))))))))
      (initEnv (fun _ => u.length + 2) (u.length :: u)) σ' (13 * u.length + 5 + (2 * (Expr.lit 1).size + 5 + (6 +
        (2 * (Expr.lit 2).size + 5 + (2 + (2 + (44 * nA u + 6 + (4 + K)))))))) :=
    fun r => r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r)))))))
  have hho8 : s8.out = [] := by simp [s8, ho7, s6, s4, s3, s2, hout2]
  by_cases hbad : badA u = true
  · have r9 : Run B (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 1)))) s8
        { s8 with out := s8.out ++ [0] ++ [0] ++ [1] } 6 :=
      (Run.write (ev_lit (by omega))).seq ((Run.write (ev_lit (by omega))).seq (Run.write (ev_lit (by omega))))
    have r := (Run.ite_true (c := .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 1))))
      (d := goodCom) (by rw [hcond]; simp [hbad]) r9)
    refine ⟨_, (pre r).mono ?_, ?_⟩
    · simp only [Expr.size, size_condEq]; nlinarith
    · simp [hho8, parseWord, hbad]
  · obtain ⟨s9, r9, ho9⟩ := run_good bd hc8
    have r := (Run.ite_false (c := .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 1))))
      (d := goodCom) (by rw [hcond]; simp [hbad]) r9)
    refine ⟨_, (pre r).mono ?_, ?_⟩
    · simp only [Expr.size, size_condEq]
      have : (33 * u.length + 300) * nA u ≤ (33 * u.length + 300) * u.length := Nat.mul_le_mul_left _ hn
      nlinarith
    · rw [ho9, hho8]
      unfold parseWord
      rw [if_neg hbad, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.nil_append, List.append_assoc, List.cons_append]
      rfl

theorem parseWord_le (u : List ℕ) :
    ∀ v ∈ parseWord u, v ≤ u.length * mx u + mx u + u.length * u.length + u.length + 1 := by
  intro v hv
  have hM : ∀ j, u.getD j 0 ≤ mx u := getD_le_max u
  have hn := nA_le u
  have hW := WA_le u
  unfold parseWord at hv
  split_ifs at hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  · simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.mem_flatMap,
      List.not_mem_nil, or_false] at hv
    rcases hv with (((((rfl | rfl | rfl) | ⟨j, -, rfl⟩) | ⟨j, -, rfl⟩) | ⟨j, -, rfl⟩) | ⟨i, hi, rfl⟩) |
      ⟨j, -, t, -, rfl⟩
    · omega
    · have := hM 2; unfold mA; omega
    · omega
    · have := hM (posA u j + 2); unfold pA; omega
    · have := hM (objA u + 3 * j + 2); unfold dA; omega
    · have := hM (objA u + 3 * j + 1); unfold wA; omega
    · have h1 := offA_le u i
      have h2 : i * u.length ≤ (u.length + 1) * u.length := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · have := hM (posA u j + mA u + 6 + 3 * t); unfold mchA; omega

/-- **Reading the standard word is polynomial.** -/
theorem parseWord_polytime : Lax759944.RamPolytime.RamPolytime parseWord := by
  refine ramPolytime_of_runs pwLayout pwCom parseWord bndCW (fun u => 400 * (u.length + 1) ^ 2) 4001 2
    pwCom_ok (fun u v hv => ?_) run_pw (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
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
    have h3 : 2 ^ (2 * bitSize u + 10) ≤ 2 ^ (4001 * (bitSize u + 1) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    refine le_trans ?_ h3
    simp only [Layout.span, pwLayout, List.length_cons, List.length_nil, bndCW]
    generalize (u.length + mx u + 8) ^ 2 = b at h
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const]
    nlinarith
  · refine lt_of_lt_of_le ?_ (pow_mono_fit2 u (by norm_num))
    have h := sq_fit8 u 1 (by norm_num)
    have h1 := parseWord_le u v hv
    have h2 : u.length * mx u + mx u + u.length * u.length + u.length + 1 ≤ 8 * (u.length + mx u + 8) ^ 2 := by
      nlinarith
    omega

end PW

end Lax434175Proofs.P200Programs
