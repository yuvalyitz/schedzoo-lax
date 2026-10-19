import Mathlib.Tactic
import Lax434175Proofs.JitDomination
import Lax434175Proofs.JitEmit

/-!
The IMP+ program of the word map `JitDomination.dsTok`: read the word, and when it can be read as
a graph with `k ≤ n`, write `n + 2`, `n + 2`, `k + 2`, then for every vertex `v` the size and the
members of its closed neighbourhood, testing every `u < n` by a scan of the whole word for an
entry of the block of `v` equal to `u`, and the two sets `{n}` and `{n + 1}`; otherwise write the
numbers of the fixed no-instance. Every loop is bounded by the length of the word, so the program
runs in cubic time on every word.
-/

namespace Lax434175Proofs.JitDomProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.JitDomination
open Lax434175Proofs.Cost (forLoop run_forLoop rdG run_rdG)
open Lax434175Proofs.Sanity.Emit (writeList run_writeList)
open Lax434175Proofs.ThresholdProgram (ev_lit ev_var ev_add ev_sub)
open Lax434175Proofs.JitEmit (V add sub incr dtrue dfalse btrue bfalse arr_eq)

/-! ### The program -/

/-- Read `n` and `k`. -/
def headCom : Com :=
  .seq (rdG "a" "L" "n" (.lit 0)) (rdG "a" "L" "k" (sub (V "L") (.lit 1)))

/-- The test of one position `j`: it lies in the block of `v` and holds `u`. -/
def tstCom : Com :=
  .ite (.lt (V "j") (V "lo")) .skip
    (.ite (.lt (V "j") (V "hi")) (.ite (.eq (V "t") (V "u")) (.assign "f" (.lit 1)) .skip) .skip)

def jBody : Com := .seq (rdG "a" "L" "t" (add (V "b") (V "j"))) (.seq tstCom (incr "j"))

/-- `f := 1` if `u` lies in the closed neighbourhood of `v`, else `f := 0`. -/
def flagCom : Com :=
  .seq (.ite (.eq (V "u") (V "v")) (.assign "f" (.lit 1)) (.assign "f" (.lit 0))) (forLoop "j" "L" jBody)

def cntBody : Com := .seq flagCom (.seq (.assign "c" (add (V "c") (V "f"))) (incr "u"))

def wrBody : Com := .seq flagCom (.seq (.ite (.eq (V "f") (.lit 1)) (.write (V "u")) .skip) (incr "u"))

/-- The block of vertex `v`: the size of its closed neighbourhood and its members. -/
def vBody : Com :=
  .seq (rdG "a" "L" "lo" (add (V "v") (.lit 2))) <| .seq (rdG "a" "L" "hi" (add (V "v") (.lit 3))) <|
  .seq (.assign "c" (.lit 0)) <| .seq (forLoop "u" "n" cntBody) <| .seq (.write (V "c")) <|
  .seq (forLoop "u" "n" wrBody) (incr "v")

/-- The numbers of the closed-neighbourhood instance. -/
def mainCom : Com :=
  .seq (.write (add (V "n") (.lit 2))) <| .seq (.write (add (V "n") (.lit 2))) <|
  .seq (.write (add (V "k") (.lit 2))) <| .seq (.assign "b" (add (V "n") (.lit 3))) <|
  .seq (forLoop "v" "n" vBody) <| .seq (writeList [1]) <| .seq (.write (V "n")) <|
  .seq (writeList [1]) (.write (add (V "n") (.lit 1)))

/-- The program. -/
def dsCom : Com :=
  .seq Lax434175Proofs.Sanity.ReadAll.readAll <| .seq headCom <|
    .ite (.lt (add (V "n") (.lit 2)) (V "L"))
      (.ite (.lt (V "k") (add (V "n") (.lit 1))) mainCom (writeList noToks)) (writeList noToks)

/-! ### Facts on the word -/

variable (x : List ℕ)

/-- The largest entry. -/
abbrev M : ℕ := Lax434175.Results.maxEntry x

theorem getD_le (q : ℕ) : x.getD q 0 ≤ M x := Lax434175Proofs.IsemPrograms.getD_le_max x q

/-- `u` is in the closed neighbourhood of `v` by the positions below `r`. -/
def Hit (v u r : ℕ) : Prop :=
  u = v ∨ ∃ j < r, x.getD (v + 2) 0 ≤ j ∧ j < x.getD (v + 3) 0 ∧ x.getD (nV x + 3 + j) 0 = u

instance (v u r : ℕ) : Decidable (Hit x v u r) := inferInstanceAs (Decidable (_ ∨ _))

theorem hit_zero (v u : ℕ) : Hit x v u 0 ↔ u = v := by simp [Hit]

theorem hit_succ (v u r : ℕ) : Hit x v u (r + 1) ↔ Hit x v u r ∨
    (x.getD (v + 2) 0 ≤ r ∧ r < x.getD (v + 3) 0 ∧ x.getD (nV x + 3 + r) 0 = u) := by
  unfold Hit
  constructor
  · rintro (h | ⟨j, hj, h⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Or.inl (Or.inr ⟨j, hj, h⟩)
      · exact Or.inr h
  · rintro ((h | ⟨j, hj, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨j, by omega, h⟩
    · exact Or.inr ⟨r, by omega, h⟩

/-- What every phase after the header needs. -/
structure Ctx (σ : Env) : Prop where
  a : σ.arrs "a" = arrOf x.length fun q => x.getD q 0
  L : σ.vars "L" = x.length
  n : σ.vars "n" = nV x
  b : σ.vars "b" = nV x + 3
  nL : nV x + 3 ≤ x.length

variable {x}

theorem Ctx.of {σ τ : Env} (h : Ctx x σ) (hv : ∀ y ∈ ["L", "n", "b"], τ.vars y = σ.vars y)
    (ha : τ.arrs "a" = σ.arrs "a") : Ctx x τ :=
  ⟨by rw [ha, h.a], by rw [hv "L" (by simp), h.L], by rw [hv "n" (by simp), h.n],
    by rw [hv "b" (by simp), h.b], h.nL⟩

/-- The frame of a phase that writes nothing: the scalars outside `ws`, the arrays and the output
are unchanged. -/
def Fr (ws : List String) (σ τ : Env) : Prop :=
  (∀ y ∉ ws, τ.vars y = σ.vars y) ∧ τ.arrs = σ.arrs ∧ τ.out = σ.out

theorem Fr.refl (ws : List String) (σ : Env) : Fr ws σ σ := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Fr.set {ws : List String} {σ τ : Env} (h : Fr ws σ τ) {y : String} (hy : y ∈ ws) (v : ℕ) :
    Fr ws σ (τ.setVar y v) :=
  ⟨fun z hz => by
    have : z ≠ y := fun e => hz (e ▸ hy)
    simp [Env.setVar, this, h.1 z hz], h.2.1, h.2.2⟩

theorem Fr.trans {ws : List String} {σ τ ρ : Env} (h : Fr ws σ τ) (h' : Fr ws τ ρ) : Fr ws σ ρ :=
  ⟨fun z hz => (h'.1 z hz).trans (h.1 z hz), h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Fr.mono {ws ws' : List String} {σ τ : Env} (h : Fr ws σ τ) (hw : ∀ y ∈ ws, y ∈ ws') :
    Fr ws' σ τ :=
  ⟨fun z hz => h.1 z fun h' => hz (hw z h'), h.2.1, h.2.2⟩

/-- The frame of a phase that may write: the scalars outside `ws` and the arrays are unchanged. -/
def Fv (ws : List String) (σ τ : Env) : Prop := (∀ y ∉ ws, τ.vars y = σ.vars y) ∧ τ.arrs = σ.arrs

theorem Fv.refl (ws : List String) (σ : Env) : Fv ws σ σ := ⟨fun _ _ => rfl, rfl⟩

theorem Fv.set {ws : List String} {σ τ : Env} (h : Fv ws σ τ) {y : String} (hy : y ∈ ws) (v : ℕ) :
    Fv ws σ (τ.setVar y v) :=
  ⟨fun z hz => by
    have : z ≠ y := fun e => hz (e ▸ hy)
    simp [Env.setVar, this, h.1 z hz], h.2⟩

theorem Fv.trans {ws : List String} {σ τ ρ : Env} (h : Fv ws σ τ) (h' : Fv ws τ ρ) : Fv ws σ ρ :=
  ⟨fun z hz => (h'.1 z hz).trans (h.1 z hz), h'.2.trans h.2⟩

theorem Fv.of_fr {ws ws' : List String} {σ τ : Env} (h : Fr ws σ τ) (hw : ∀ y ∈ ws, y ∈ ws') :
    Fv ws' σ τ :=
  ⟨fun z hz => h.1 z fun h' => hz (hw z h'), h.2.1⟩

theorem Fv.write {ws : List String} {σ τ : Env} (h : Fv ws σ τ) (l : List ℕ) :
    Fv ws σ { τ with out := l } := h

theorem Fv.ctx {ws : List String} {σ τ : Env} (h : Fv ws σ τ) (hc : Ctx x σ) (hL : "L" ∉ ws)
    (hn : "n" ∉ ws) (hb : "b" ∉ ws) : Ctx x τ :=
  hc.of (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact h.1 _ hL
    · exact h.1 _ hn
    · exact h.1 _ hb) (by rw [h.2])

/-- The scalars a vertex's block writes. -/
abbrev vws : List String := ["v", "lo", "hi", "c", "u", "j", "t", "f"]


theorem filter_succ (p : ℕ → Prop) [DecidablePred p] (r : ℕ) :
    (List.range (r + 1)).filter (fun u => decide (p u)) =
      (List.range r).filter (fun u => decide (p u)) ++ if p r then [r] else [] := by
  rw [List.range_succ, List.filter_append]
  split_ifs with h <;> simp [h]

@[simp] theorem setVar_self (σ : Env) (y : String) (v : ℕ) : (σ.setVar y v).vars y = v := by
  simp [Env.setVar]

/-! ### The scan -/

section Scan
variable {B : ℕ} (hB : x.length + M x + 10 ≤ B)
include hB

theorem tst_run (σ : Env) {r lo hi t u : ℕ} (hj : σ.vars "j" = r) (hlo : σ.vars "lo" = lo)
    (hhi : σ.vars "hi" = hi) (ht : σ.vars "t" = t) (hu : σ.vars "u" = u)
    (hr : r < B) (hlo' : lo < B) (hhi' : hi < B) (ht' : t < B) (hu' : u < B) :
    ∃ σ', Run B tstCom σ σ' 20 ∧
      σ' = if lo ≤ r ∧ r < hi ∧ t = u then σ.setVar "f" 1 else σ := by
  have c1 : (Cond.lt (V "j") (V "lo")).evalB B σ = some (decide (r < lo)) :=
    evalB_condLt (ev_var hj hr) (ev_var hlo hlo')
  have c2 : (Cond.lt (V "j") (V "hi")).evalB B σ = some (decide (r < hi)) :=
    evalB_condLt (ev_var hj hr) (ev_var hhi hhi')
  have c3 : (Cond.eq (V "t") (V "u")).evalB B σ = some (t == u) :=
    evalB_condEq (ev_var ht ht') (ev_var hu hu')
  by_cases h1 : r < lo
  · exact ⟨σ, (Run.ite_true (by rw [c1]; exact dtrue h1) Run.skip).mono (by simp),
      by rw [if_neg (by omega)]⟩
  · by_cases h2 : r < hi
    · by_cases h3 : t = u
      · exact ⟨_, (Run.ite_false (by rw [c1]; exact dfalse h1) (Run.ite_true (by rw [c2]; exact dtrue h2)
          (Run.ite_true (by rw [c3]; exact btrue h3) (Run.assign (x := "f") (ev_lit (n := 1) (by omega)))))).mono
          (by simp), by rw [if_pos ⟨by omega, h2, h3⟩]⟩
      · exact ⟨_, (Run.ite_false (by rw [c1]; exact dfalse h1) (Run.ite_true (by rw [c2]; exact dtrue h2)
          (Run.ite_false (by rw [c3]; exact bfalse h3) Run.skip))).mono (by simp),
          by rw [if_neg (by tauto)]⟩
    · exact ⟨σ, (Run.ite_false (by rw [c1]; exact dfalse h1) (Run.ite_false (by rw [c2]; exact dfalse h2)
        Run.skip)).mono (by simp), by rw [if_neg (by omega)]⟩

variable (x) in
/-- The state of the scan for `u` in the block of `v` after `r` positions. -/
structure JInv (v u : ℕ) (σ0 : Env) (r : ℕ) (τ : Env) : Prop where
  j : τ.vars "j" = r
  f : τ.vars "f" = if Hit x v u r then 1 else 0
  fr : Fr ["j", "t", "f"] σ0 τ

theorem jBody_run {v u : ℕ} (hu : u < nV x) (σ0 : Env) (hc : Ctx x σ0)
    (hlo : σ0.vars "lo" = x.getD (v + 2) 0) (hhi : σ0.vars "hi" = x.getD (v + 3) 0)
    (huv : σ0.vars "u" = u) (r : ℕ) (hr : r < x.length) (τ : Env) (hi : JInv x v u σ0 r τ) :
    ∃ τ', Run B jBody τ τ' 40 ∧ JInv x v u σ0 (r + 1) τ' := by
  have hc' : Ctx x τ := hc.of (fun y hy => hi.fr.1 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl <;> decide))
    (by rw [hi.fr.2.1])
  have hn := getD_le x 0
  have hidx : (add (V "b") (V "j")).evalB B τ = some (nV x + 3 + r) :=
    ev_add (ev_var hc'.b (by unfold nV at *; omega)) (ev_var hi.j (by omega)) (by unfold nV at *; omega)
  have r1 := run_rdG (B := B) (a := "a") (L := "L") (v := "t") (σ := τ) (u := x) hc'.a hc'.L le_rfl
    hidx (fun j => by have := getD_le x j; omega) (by omega)
  set τ1 := τ.setVar "t" (x.getD (nV x + 3 + r) 0) with hτ1
  have hlo1 : τ1.vars "lo" = x.getD (v + 2) 0 := by
    rw [show τ1.vars "lo" = τ.vars "lo" from by simp [hτ1, Env.setVar], hi.fr.1 "lo" (by decide), hlo]
  have hhi1 : τ1.vars "hi" = x.getD (v + 3) 0 := by
    rw [show τ1.vars "hi" = τ.vars "hi" from by simp [hτ1, Env.setVar], hi.fr.1 "hi" (by decide), hhi]
  have hu1 : τ1.vars "u" = u := by rw [show τ1.vars "u" = τ.vars "u" from by simp [hτ1, Env.setVar], hi.fr.1 "u" (by decide), huv]
  obtain ⟨τ2, r2, hτ2⟩ := tst_run hB τ1 (r := r) (t := x.getD (nV x + 3 + r) 0)
    (by simp [hτ1, Env.setVar, hi.j]) hlo1 hhi1 (by rw [hτ1]; exact setVar_self _ _ _) hu1 (by omega) (by have := getD_le x (v + 2); omega)
    (by have := getD_le x (v + 3); omega) (by have := getD_le x (nV x + 3 + r); omega)
    (by unfold nV at *; omega)
  have hj2 : τ2.vars "j" = r := by
    rw [hτ2]; split_ifs <;> simp [hτ1, Env.setVar, hi.j]
  have r3 := Run.assign (x := "j") (B := B) (σ := τ2) (ev_add (ev_var hj2 (by omega)) (ev_lit (n := 1) (by omega))
    (by omega))
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), ⟨by simp [Env.setVar], ?_, ?_⟩⟩
  · have hs := hit_succ x v u r
    have hf : (τ2.setVar "j" (r + 1)).vars "f" = τ2.vars "f" := by simp [Env.setVar]
    rw [hf, hτ2]
    by_cases hc3 : x.getD (v + 2) 0 ≤ r ∧ r < x.getD (v + 3) 0 ∧ x.getD (nV x + 3 + r) 0 = u
    · rw [if_pos hc3, if_pos (hs.mpr (Or.inr hc3))]; simp [Env.setVar]
    · rw [if_neg hc3]
      simp only [hτ1, Env.setVar, show ("f" : String) ≠ "t" by decide, if_false]
      rw [hi.f]
      by_cases hh : Hit x v u r
      · rw [if_pos hh, if_pos (hs.mpr (Or.inl hh))]
      · rw [if_neg hh, if_neg (fun h => (hs.mp h).elim hh hc3)]
  · have h1 : Fr ["j", "t", "f"] σ0 τ1 := hi.fr.set (by simp) _
    have h2 : Fr ["j", "t", "f"] σ0 τ2 := by
      rw [hτ2]; split_ifs
      · exact h1.set (by simp) _
      · exact h1
    exact h2.set (by simp) _

/-- **The scan computes the flag.** -/
theorem flag_run {v u : ℕ} (hv : v < nV x) (hu : u < nV x) (σ : Env) (hc : Ctx x σ)
    (hvv : σ.vars "v" = v) (huv : σ.vars "u" = u)
    (hlo : σ.vars "lo" = x.getD (v + 2) 0) (hhi : σ.vars "hi" = x.getD (v + 3) 0) :
    ∃ τ, Run B flagCom σ τ (44 * x.length + 20) ∧
      τ.vars "f" = (if InN x v u then 1 else 0) ∧ Fr ["j", "t", "f"] σ τ := by
  have hn := getD_le x 0
  have c0 : (Cond.eq (V "u") (V "v")).evalB B σ = some (u == v) :=
    evalB_condEq (ev_var huv (by unfold nV at *; omega)) (ev_var hvv (by unfold nV at *; omega))
  obtain ⟨σ1, r1, hf1⟩ : ∃ σ1, Run B (.ite (.eq (V "u") (V "v")) (.assign "f" (.lit 1))
      (.assign "f" (.lit 0))) σ σ1 10 ∧ σ1 = σ.setVar "f" (if u = v then 1 else 0) := by
    by_cases h : u = v
    · exact ⟨_, (Run.ite_true (by rw [c0]; exact btrue h)
        (Run.assign (x := "f") (ev_lit (n := 1) (by omega)))).mono (by simp), by rw [if_pos h]⟩
    · exact ⟨_, (Run.ite_false (by rw [c0]; exact bfalse h)
        (Run.assign (x := "f") (ev_lit (n := 0) (by omega)))).mono (by simp), by rw [if_neg h]⟩
  have hfr1 : Fr ["j", "t", "f"] σ σ1 := hf1 ▸ (Fr.refl _ σ).set (by simp) _
  have hc1 : Ctx x σ1 := hc.of (fun y hy => hfr1.1 y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl <;> decide))
    (by rw [hfr1.2.1])
  have hlo1 : σ1.vars "lo" = x.getD (v + 2) 0 := by rw [hfr1.1 "lo" (by decide), hlo]
  have hhi1 : σ1.vars "hi" = x.getD (v + 3) 0 := by rw [hfr1.1 "hi" (by decide), hhi]
  have hu1 : σ1.vars "u" = u := by rw [hfr1.1 "u" (by decide), huv]
  obtain ⟨τ, r2, hτ⟩ := run_forLoop (B := B) "j" "L" jBody x.length 40 (by omega)
    (fun r τ => JInv x v u σ1 r τ) (fun _ _ h => h.j)
    (fun _ τ h => by rw [h.fr.1 "L" (by decide), hc1.L])
    (fun r hr τ h => jBody_run hB hu σ1 hc1 hlo1 hhi1 hu1 r hr τ h)
    (σ := σ1) ⟨by simp [Env.setVar], by
      simp only [Env.setVar, show ("f" : String) ≠ "j" by decide, if_false]
      rw [hf1]; simp [Env.setVar, hit_zero], (Fr.refl _ σ1).set (by simp) _⟩
  refine ⟨τ, (r1.seq r2).mono (by omega), by rw [hτ.f]; rfl, hfr1.trans hτ.fr⟩

variable (x) in
/-- After `r` candidates of the count. -/
structure CInv (v : ℕ) (σ0 : Env) (r : ℕ) (τ : Env) : Prop where
  u : τ.vars "u" = r
  c : τ.vars "c" = ((List.range r).filter fun u => decide (InN x v u)).length
  fr : Fr ["c", "u", "j", "t", "f"] σ0 τ

theorem cntBody_run {v : ℕ} (hv : v < nV x) (σ0 : Env) (hc : Ctx x σ0) (hvv : σ0.vars "v" = v)
    (hlo : σ0.vars "lo" = x.getD (v + 2) 0) (hhi : σ0.vars "hi" = x.getD (v + 3) 0)
    (r : ℕ) (hr : r < nV x) (τ : Env) (hi : CInv x v σ0 r τ) :
    ∃ τ', Run B cntBody τ τ' (44 * x.length + 34) ∧ CInv x v σ0 (r + 1) τ' := by
  have hc' : Ctx x τ := (Fv.of_fr hi.fr fun _ h => h).ctx hc (by decide) (by decide) (by decide)
  have hn := getD_le x 0
  obtain ⟨τ1, r1, hf1, hfr1⟩ := flag_run hB hv hr τ hc' (by rw [hi.fr.1 "v" (by decide), hvv]) hi.u
    (by rw [hi.fr.1 "lo" (by decide), hlo]) (by rw [hi.fr.1 "hi" (by decide), hhi])
  have hcl : ((List.range r).filter fun u => decide (InN x v u)).length ≤ r := by
    have := List.length_filter_le (fun u => decide (InN x v u)) (List.range r); simpa using this
  have hc1 : τ1.vars "c" = ((List.range r).filter fun u => decide (InN x v u)).length := by
    rw [hfr1.1 "c" (by decide), hi.c]
  have hu1 : τ1.vars "u" = r := by rw [hfr1.1 "u" (by decide), hi.u]
  have r2 := Run.assign (x := "c") (B := B) (σ := τ1)
    (ev_add (ev_var hc1 (by unfold nV at *; omega)) (ev_var hf1 (by split_ifs <;> omega)) (by
      unfold nV at *; split_ifs <;> omega))
  set τ2 := τ1.setVar "c" (((List.range r).filter fun u => decide (InN x v u)).length +
    if InN x v r then 1 else 0) with hτ2
  have r3 := Run.assign (x := "u") (B := B) (σ := τ2)
    (ev_add (ev_var (x := "u") (v := r) (by simp [hτ2, Env.setVar, hu1]) (by unfold nV at *; omega))
      (ev_lit (n := 1) (by omega)) (by unfold nV at *; omega))
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), ⟨by simp [Env.setVar], ?_, ?_⟩⟩
  · simp only [Env.setVar, show ("c" : String) ≠ "u" by decide, if_false, if_true, hτ2]
    rw [filter_succ]
    split_ifs <;> simp
  · exact ((hi.fr.trans (hfr1.mono (by simp))).set (by simp) _).set (by simp) _

variable (x) in
/-- After `r` candidates of the writing. -/
structure WInv (v : ℕ) (σ0 : Env) (r : ℕ) (τ : Env) : Prop where
  u : τ.vars "u" = r
  out : τ.out = σ0.out ++ (List.range r).filter fun u => decide (InN x v u)
  fr : Fv ["u", "j", "t", "f"] σ0 τ

theorem wrBody_run {v : ℕ} (hv : v < nV x) (σ0 : Env) (hc : Ctx x σ0) (hvv : σ0.vars "v" = v)
    (hlo : σ0.vars "lo" = x.getD (v + 2) 0) (hhi : σ0.vars "hi" = x.getD (v + 3) 0)
    (r : ℕ) (hr : r < nV x) (τ : Env) (hi : WInv x v σ0 r τ) :
    ∃ τ', Run B wrBody τ τ' (44 * x.length + 35) ∧ WInv x v σ0 (r + 1) τ' := by
  have hc' : Ctx x τ := hi.fr.ctx hc (by decide) (by decide) (by decide)
  have hn := getD_le x 0
  obtain ⟨τ1, r1, hf1, hfr1⟩ := flag_run hB hv hr τ hc' (by rw [hi.fr.1 "v" (by decide), hvv]) hi.u
    (by rw [hi.fr.1 "lo" (by decide), hlo]) (by rw [hi.fr.1 "hi" (by decide), hhi])
  have hu1 : τ1.vars "u" = r := by rw [hfr1.1 "u" (by decide), hi.u]
  have c1 : (Cond.eq (V "f") (.lit 1)).evalB B τ1 = some ((if InN x v r then 1 else 0) == 1) :=
    evalB_condEq (ev_var hf1 (by split_ifs <;> omega)) (ev_lit (by omega))
  obtain ⟨τ2, r2, ho2, hv2, ha2⟩ : ∃ τ2, Run B (.ite (.eq (V "f") (.lit 1)) (.write (V "u")) .skip) τ1 τ2 6 ∧
      τ2.out = τ1.out ++ (if InN x v r then [r] else []) ∧ τ2.vars = τ1.vars ∧ τ2.arrs = τ1.arrs := by
    by_cases h : InN x v r
    · exact ⟨_, (Run.ite_true (by rw [c1, if_pos h]; rfl)
        (Run.write (ev_var hu1 (by unfold nV at *; omega)))).mono (by simp), by simp [h], rfl, rfl⟩
    · exact ⟨_, (Run.ite_false (by rw [c1, if_neg h]; rfl) Run.skip).mono (by simp), by simp [h],
        rfl, rfl⟩
  have r3 := Run.assign (x := "u") (B := B) (σ := τ2)
    (ev_add (ev_var (x := "u") (v := r) (by rw [hv2, hu1]) (by unfold nV at *; omega))
      (ev_lit (n := 1) (by omega)) (by unfold nV at *; omega))
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), ⟨by simp [Env.setVar], ?_, ?_⟩⟩
  · simp only [Env.setVar]
    rw [ho2, hfr1.2.2, hi.out, filter_succ, List.append_assoc]
  · have h1 : Fv ["u", "j", "t", "f"] σ0 τ1 := hi.fr.trans (Fv.of_fr hfr1 (by simp))
    have h2 : Fv ["u", "j", "t", "f"] σ0 τ2 := ⟨fun z hz => by rw [hv2]; exact h1.1 z hz, by rw [ha2]; exact h1.2⟩
    exact h2.set (by simp) _

/-- The block of vertex `v` in the numbers. -/
def blkV (v : ℕ) : List ℕ := (nbhd x v).length :: nbhd x v

/-- The cost of the block of a vertex. -/
def Kv (L n : ℕ) : ℕ := 88 * L * n + 77 * n + 42

variable (x) in
/-- After `r` vertices. -/
structure VInv (σ0 : Env) (r : ℕ) (τ : Env) : Prop where
  v : τ.vars "v" = r
  out : τ.out = σ0.out ++ (List.range r).flatMap (blkV (x := x))
  fr : Fv vws σ0 τ

theorem vBody_run (σ0 : Env) (hc : Ctx x σ0) (r : ℕ) (hr : r < nV x) (τ : Env) (hi : VInv x σ0 r τ) :
    ∃ τ', Run B vBody τ τ' (Kv x.length (nV x)) ∧ VInv x σ0 (r + 1) τ' := by
  have hc' : Ctx x τ := hi.fr.ctx hc (by decide) (by decide) (by decide)
  have hn := getD_le x 0
  have huB : ∀ j, x.getD j 0 < B := fun j => by have := getD_le x j; omega
  have r1 := run_rdG (B := B) (a := "a") (L := "L") (v := "lo") (σ := τ) (u := x) hc'.a hc'.L le_rfl
    (ev_add (ev_var hi.v (by unfold nV at *; omega)) (ev_lit (n := 2) (by omega)) (by unfold nV at *; omega))
    huB (by omega)
  set τ1 := τ.setVar "lo" (x.getD (r + 2) 0) with hτ1
  have r2 := run_rdG (B := B) (a := "a") (L := "L") (v := "hi") (σ := τ1) (u := x)
    (by simp [hτ1, Env.setVar, hc'.a]) (by simp [hτ1, Env.setVar, hc'.L]) le_rfl
    (ev_add (ev_var (x := "v") (v := r) (by simp [hτ1, Env.setVar, hi.v]) (by unfold nV at *; omega))
      (ev_lit (n := 3) (by omega)) (by unfold nV at *; omega)) huB (by omega)
  set τ2 := τ1.setVar "hi" (x.getD (r + 3) 0) with hτ2
  have r3 := Run.assign (x := "c") (B := B) (σ := τ2) (ev_lit (n := 0) (by omega))
  set τ3 := τ2.setVar "c" 0 with hτ3
  have hfr3 : Fv vws τ τ3 := Fv.set (Fv.set (Fv.set (Fv.refl vws τ) (by simp) _) (by simp) _) (by simp) _
  have hc3 : Ctx x τ3 := hfr3.ctx hc' (by decide) (by decide) (by decide)
  have hv3 : τ3.vars "v" = r := by simp [hτ3, hτ2, hτ1, Env.setVar, hi.v]
  have hlo3 : τ3.vars "lo" = x.getD (r + 2) 0 := by
    rw [hτ3, hτ2]; simp only [Env.setVar, show ("lo" : String) ≠ "c" by decide,
      show ("lo" : String) ≠ "hi" by decide, if_false]; rw [hτ1]; exact setVar_self _ _ _
  have hhi3 : τ3.vars "hi" = x.getD (r + 3) 0 := by
    rw [hτ3]; simp only [Env.setVar, show ("hi" : String) ≠ "c" by decide, if_false]
    rw [hτ2]; exact setVar_self _ _ _
  obtain ⟨τ4, r4, hτ4⟩ := run_forLoop (B := B) "u" "n" cntBody (nV x) (44 * x.length + 34)
    (by unfold nV at *; omega) (fun k τ => CInv x r τ3 k τ) (fun _ _ h => h.u)
    (fun _ τ h => by rw [h.fr.1 "n" (by decide), hc3.n])
    (fun k hk τ h => cntBody_run hB hr τ3 hc3 hv3 hlo3 hhi3 k hk τ h)
    (σ := τ3) ⟨by simp [Env.setVar], by simp [Env.setVar, hτ3], (Fr.refl _ τ3).set (by simp) _⟩
  have hc4 : τ4.vars "c" = (nbhd x r).length := hτ4.c
  have r5 := Run.write (B := B) (σ := τ4) (e := V "c") (ev_var hc4 (by
    have := List.length_filter_le (fun u => decide (InN x r u)) (List.range (nV x))
    simp at this; unfold nbhd; unfold nV at *; omega))
  set τ5 : Env := { τ4 with out := τ4.out ++ [(nbhd x r).length] } with hτ5
  have hfr5 : Fv ["c", "u", "j", "t", "f"] τ3 τ5 := (Fv.of_fr hτ4.fr (by simp)).write _
  have hc5 : Ctx x τ5 := hfr5.ctx hc3 (by decide) (by decide) (by decide)
  obtain ⟨τ6, r6, hτ6⟩ := run_forLoop (B := B) "u" "n" wrBody (nV x) (44 * x.length + 35)
    (by unfold nV at *; omega) (fun k τ => WInv x r τ5 k τ) (fun _ _ h => h.u)
    (fun _ τ h => by rw [h.fr.1 "n" (by decide), hc5.n])
    (fun k hk τ h => wrBody_run hB hr τ5 hc5 (by rw [hfr5.1 "v" (by decide), hv3])
      (by rw [hfr5.1 "lo" (by decide), hlo3]) (by rw [hfr5.1 "hi" (by decide), hhi3]) k hk τ h)
    (σ := τ5) ⟨by simp [Env.setVar], by simp [Env.setVar], ⟨fun z hz => by
      simp at hz; simp [Env.setVar, hz], rfl⟩⟩
  have hv6 : τ6.vars "v" = r := by rw [hτ6.fr.1 "v" (by decide), hfr5.1 "v" (by decide), hv3]
  have r7 := Run.assign (x := "v") (B := B) (σ := τ6) (ev_add (ev_var hv6 (by unfold nV at *; omega))
    (ev_lit (n := 1) (by omega)) (by unfold nV at *; omega))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_, ⟨by simp [Env.setVar], ?_, ?_⟩⟩
  · unfold Kv; simp; ring_nf; omega
  · show τ6.out = _
    rw [hτ6.out, List.range_succ, List.flatMap_append, ← List.append_assoc, ← hi.out]
    show τ4.out ++ [(nbhd x r).length] ++ _ = _
    rw [hτ4.fr.2.2, show τ3.out = τ.out from rfl]
    simp [blkV, nbhd]
  · have h56 : Fv vws τ3 τ6 := ⟨fun z hz => by
      rw [hτ6.fr.1 z (fun h => hz (by simp at h ⊢; tauto)),
        hfr5.1 z (fun h => hz (by simp at h ⊢; tauto))], hτ6.fr.2.trans hfr5.2⟩
    exact (hi.fr.trans (hfr3.trans h56)).set (by simp) _

/-- **The numbers of the closed-neighbourhood instance are written.** -/
theorem mainCom_run (σ : Env) (ha : σ.arrs "a" = arrOf x.length fun q => x.getD q 0)
    (hL : σ.vars "L" = x.length) (hn : σ.vars "n" = nV x) (hk : σ.vars "k" = kV x) (hg : Good x) :
    ∃ τ, Run B mainCom σ τ ((Kv x.length (nV x) + 4) * nV x + 40) ∧
      τ.out = σ.out ++ ([nV x + 2, nV x + 2, kV x + 2] ++
        (List.range (nV x)).flatMap (fun v => (nbhd x v).length :: nbhd x v) ++
          [1, nV x, 1, nV x + 1]) := by
  have hn0 := getD_le x 0
  have hk0 := getD_le x (x.length - 1)
  have hnM : nV x ≤ M x := hn0
  have hkM : kV x ≤ M x := hk0
  have w1 := Run.write (B := B) (σ := σ) (ev_add (ev_var hn (by omega)) (ev_lit (n := 2) (by omega))
    (by omega))
  set σ1 : Env := { σ with out := σ.out ++ [nV x + 2] } with hσ1
  have w2 := Run.write (B := B) (σ := σ1) (ev_add (ev_var (x := "n") hn (by omega))
    (ev_lit (n := 2) (by omega)) (by omega))
  set σ2 : Env := { σ1 with out := σ1.out ++ [nV x + 2] } with hσ2
  have w3 := Run.write (B := B) (σ := σ2) (ev_add (ev_var (x := "k") hk (by omega))
    (ev_lit (n := 2) (by omega)) (by omega))
  set σ3 : Env := { σ2 with out := σ2.out ++ [kV x + 2] } with hσ3
  have a4 := Run.assign (x := "b") (B := B) (σ := σ3) (ev_add (ev_var (x := "n") hn (by omega))
    (ev_lit (n := 3) (by omega)) (by omega))
  set σ4 := σ3.setVar "b" (nV x + 3) with hσ4
  have hc4 : Ctx x σ4 := ⟨by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, ha], by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hL],
    by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hn], by simp [hσ4], hg.1⟩
  obtain ⟨σ5, r5, h5⟩ := run_forLoop (B := B) "v" "n" vBody (nV x) (Kv x.length (nV x)) (by omega)
    (fun r τ => VInv x σ4 r τ) (fun _ _ h => h.v) (fun _ τ h => by rw [h.fr.1 "n" (by decide), hc4.n])
    (fun r hr τ h => vBody_run hB σ4 hc4 r hr τ h)
    (σ := σ4) ⟨by simp [Env.setVar], by simp [Env.setVar], (Fv.refl _ σ4).set (by simp) _⟩
  have hn5 : σ5.vars "n" = nV x := by rw [h5.fr.1 "n" (by decide), hc4.n]
  have w6 := run_writeList (B := B) σ5 [1] (by simp; omega)
  set σ6 : Env := { σ5 with out := σ5.out ++ [1] } with hσ6
  have w7 := Run.write (B := B) (σ := σ6) (ev_var (x := "n") (v := nV x) hn5 (by omega))
  set σ7 : Env := { σ6 with out := σ6.out ++ [nV x] } with hσ7
  have w8 := run_writeList (B := B) σ7 [1] (by simp; omega)
  set σ8 : Env := { σ7 with out := σ7.out ++ [1] } with hσ8
  have w9 := Run.write (B := B) (σ := σ8) (ev_add (ev_var (x := "n") (v := nV x) hn5 (by omega))
    (ev_lit (n := 1) (by omega)) (by omega))
  refine ⟨_, (w1.seq (w2.seq (w3.seq (a4.seq (r5.seq (w6.seq (w7.seq (w8.seq w9)))))))).mono
    (by simp; omega), ?_⟩
  simp only [hσ8, hσ7, hσ6, h5.out, hσ4, hσ3, hσ2, hσ1, Env.setVar, List.append_assoc,
    List.cons_append, List.nil_append]
  rfl

end Scan

/-! ### The whole run -/

variable (x)

/-- The value bound. -/
def bndD : ℕ := x.length + M x + 10

/-- The cost bound. -/
def costD (L : ℕ) : ℕ := 400 * (L + 1) ^ 3 + 200

theorem cost_le {L n : ℕ} (h : n ≤ L) : (Kv L n + 4) * n + 40 ≤ 300 * (L + 1) ^ 3 := by
  unfold Kv
  have h1 : L * n ≤ (L + 1) ^ 2 := by nlinarith
  have h2 : n ≤ (L + 1) ^ 2 := by nlinarith
  have h3 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 88 * L * n + 77 * n + 42 + 4 ≤ 211 * (L + 1) ^ 2 := by nlinarith
  have h5 : (88 * L * n + 77 * n + 42 + 4) * n ≤ 211 * (L + 1) ^ 2 * (L + 1) :=
    Nat.mul_le_mul h4 (by omega)
  have h6 : (L + 1) ^ 3 = (L + 1) ^ 2 * (L + 1) := by ring
  have h7 : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- **The program writes the word map.** -/
theorem run_ds :
    ∃ σ', Run (bndD x) dsCom (initEnv (fun _ => x.length) (x.length :: x)) σ'
      (costD x.length) ∧ σ'.out = dsTok x := by
  set B := bndD x with hBd
  have hB : x.length + M x + 10 ≤ B := le_rfl
  have hyB : ∀ v ∈ x, v < B := fun v hv => by
    have := Lax434175Proofs.PadWord.le_foldr_max hv
    unfold M Lax434175.Results.maxEntry at *; omega
  have huB : ∀ j, x.getD j 0 < B := fun j => by have := getD_le x j; omega
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, -, -, -, -⟩ :=
    (Lax434175Proofs.Sanity.ReadAll.readAll_spec (B := B) (y := x) hyB (by omega)).frame
      (initEnv (fun _ => x.length) (x.length :: x)) ⟨rfl, rfl, by simp [initEnv]⟩
  have ha1' : σ1.arrs "a" = arrOf x.length fun q => x.getD q 0 := by rw [ha1, arr_eq]
  have r2 := run_rdG (B := B) (a := "a") (L := "L") (v := "n") (σ := σ1) (u := x) ha1' hL1 le_rfl
    (evalB_lit (n := 0) (by omega)) huB (by omega)
  set σ2 := σ1.setVar "n" (x.getD 0 0) with hσ2
  have r3 := run_rdG (B := B) (a := "a") (L := "L") (v := "k") (σ := σ2) (u := x)
    (by simp [hσ2, Env.setVar, ha1']) (by simp [hσ2, Env.setVar, hL1]) le_rfl
    (ev_sub (ev_var (x := "L") (v := x.length) (by simp [hσ2, Env.setVar, hL1]) (by omega))
      (ev_lit (n := 1) (by omega))) huB (by omega)
  set σ3 := σ2.setVar "k" (x.getD (x.length - 1) 0) with hσ3
  have hn3 : σ3.vars "n" = nV x := by simp [hσ3, hσ2, Env.setVar]; rfl
  have hk3 : σ3.vars "k" = kV x := by rw [hσ3]; exact setVar_self _ _ _
  have hL3 : σ3.vars "L" = x.length := by simp [hσ3, hσ2, Env.setVar, hL1]
  have ha3 : σ3.arrs "a" = arrOf x.length fun q => x.getD q 0 := by simp [hσ3, hσ2, Env.setVar, ha1']
  have ho3 : σ3.out = [] := by simp [hσ3, hσ2, Env.setVar, ho1]
  have hnM : nV x ≤ M x := getD_le x 0
  have hkM : kV x ≤ M x := getD_le x _
  have c1 : (Cond.lt (add (V "n") (.lit 2)) (V "L")).evalB B σ3 =
      some (decide (nV x + 2 < x.length)) :=
    evalB_condLt (ev_add (ev_var hn3 (by omega)) (ev_lit (by omega)) (by omega)) (ev_var hL3 (by omega))
  have c2 : (Cond.lt (V "k") (add (V "n") (.lit 1))).evalB B σ3 = some (decide (kV x < nV x + 1)) :=
    evalB_condLt (ev_var hk3 (by omega)) (ev_add (ev_var hn3 (by omega)) (ev_lit (by omega)) (by omega))
  have hno : ∀ v ∈ noToks, v < B := by intro v hv; simp [noToks] at hv; omega
  have hl3 : x.length + 1 ≤ (x.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  by_cases h1 : nV x + 2 < x.length
  · by_cases h2 : kV x < nV x + 1
    · have hg : Good x := ⟨by omega, by omega⟩
      obtain ⟨σ4, r4, ho4⟩ := mainCom_run hB σ3 ha3 hL3 hn3 hk3 hg
      refine ⟨σ4, (r1.seq ((r2.seq r3).seq (Run.ite_true (by rw [c1]; exact dtrue h1)
        (Run.ite_true (by rw [c2]; exact dtrue h2) r4)))).mono ?_, by rw [ho4, ho3, dsTok, if_pos hg]; rfl⟩
      have := cost_le (L := x.length) (n := nV x) (by omega)
      simp only [size_condLt, Expr.size]
      unfold costD
      omega
    · have hg : ¬ Good x := fun h => h2 (by have := h.2; omega)
      refine ⟨_, (r1.seq ((r2.seq r3).seq (Run.ite_true (by rw [c1]; exact dtrue h1)
        (Run.ite_false (by rw [c2]; exact dfalse h2) (run_writeList σ3 noToks hno))))).mono ?_,
        by simp [ho3, dsTok, if_neg hg]⟩
      have : 1 ≤ (x.length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      simp only [size_condLt, Expr.size, noToks, List.length_cons,
        List.length_nil]
      unfold costD
      omega
  · have hg : ¬ Good x := fun h => h1 (by have := h.1; omega)
    refine ⟨_, (r1.seq ((r2.seq r3).seq (Run.ite_false (by rw [c1]; exact dfalse h1)
      (run_writeList σ3 noToks hno)))).mono ?_, by simp [ho3, dsTok, if_neg hg]⟩
    have : 1 ≤ (x.length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    simp only [size_condLt, Expr.size, noToks, List.length_cons,
      List.length_nil]
    unfold costD
    omega

/-! ### Polynomial time -/

/-- The layout of the program. -/
def layoutD : Layout :=
  ⟨["L", "rt", "rv", "n", "k", "b", "v", "lo", "hi", "c", "u", "j", "t", "f"], ["a"], 12⟩

theorem dsCom_ok : Com.Ok layoutD dsCom := by
  simp [dsCom, headCom, mainCom, vBody, cntBody, wrBody, flagCom, jBody, tstCom, rdG, writeList,
    noToks, Lax434175Proofs.Sanity.ReadAll.readAll, Lax434175Proofs.Sanity.ReadAll.readLoop,
    Lax434175Proofs.Sanity.ReadAll.readBody, layoutD, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

open Lax759944.BinaryWordEncoding in
/-- **The word map is polynomial.** -/
theorem dsTok_polytime : Lax759944.RamPolytime.RamPolytime dsTok := by
  refine Lax434175Proofs.Cost.ramPolytime_of_runs layoutD dsCom dsTok bndD
    (fun u => costD u.length) 7000 3 dsCom_ok (fun u v hv => ?_)
    (fun u => ⟨_, run_ds u⟩) (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · unfold bndD
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold M Lax434175.Results.maxEntry at *
      omega
  · unfold bndD; omega
  · have h1 := Lax434175Proofs.ThresholdProgram.size_le u
    have h3 : bitSize u + 1 + 6 ≤ 7000 * (bitSize u + 1) ^ 3 := by
      have : bitSize u + 1 ≤ (bitSize u + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      omega
    have h4 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h3
    have h5 : (2 : ℕ) ^ (bitSize u + 1 + 6) = 64 * 2 ^ (bitSize u + 1) := by ring
    simp only [Layout.span, layoutD, List.length_cons, List.length_nil, max_le_iff]
    unfold bndD M at *
    constructor <;> omega
  · have hl := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const, costD]
    have : (u.length + 1) ^ 3 ≤ (bitSize u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have : 1 ≤ (bitSize u + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  · obtain ⟨σ', r, ho⟩ := run_ds u
    have hlt := Lax434175Proofs.JitEmit.Run.out_lt r (by simp [initEnv]) v (by rw [ho]; exact hv)
    have h1 := Lax434175Proofs.ThresholdProgram.size_le u
    have h3 : bitSize u + 1 + 6 ≤ 7000 * (bitSize u + 1) ^ 3 := by
      have : bitSize u + 1 ≤ (bitSize u + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      omega
    have h4 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h3
    have h5 : (2 : ℕ) ^ (bitSize u + 1 + 6) = 64 * 2 ^ (bitSize u + 1) := by ring
    unfold bndD M at *
    omega

end Lax434175Proofs.JitDomProg
