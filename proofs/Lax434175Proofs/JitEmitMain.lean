import Mathlib.Tactic
import Lax434175Proofs.JitEmitWalk
import Lax434175Proofs.JitEmitBounds

/-!
The main part of the emitter's program: the slot of a job, its processing times and due date,
the loops over the jobs.
-/

namespace Lax434175Proofs.JitEmit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.JitRaw Lax434175Proofs.JitWords
open Lax434175Proofs.Cost (forLoop run_forLoop)
open Lax434175Proofs.Sanity.Emit (writeList run_writeList)
open Lax434175Proofs.ThresholdProgram (ev_lit ev_var ev_add ev_mul ev_sub)

theorem ev_div {B : ℕ} {σ : Env} {e f : Expr} {m n : ℕ} (he : e.evalB B σ = some m)
    (hf : f.evalB B σ = some n) : (div e f).evalB B σ = some (m / n) :=
  evalB_bin he hf (lt_of_le_of_lt (Nat.div_le_self _ _) (Expr.eval_and_lt_of_evalB he).2)

/-- The state the loops over the jobs need. -/
structure MCtx (z : List ℕ) (x : HRaw) (τ : Env) : Prop where
  n : τ.vars "n" = x.n
  m : τ.vars "m" = x.m
  k : τ.vars "k" = x.k
  Q : τ.vars "Q" = x.Q
  Lm : τ.vars "Lm" = x.ML.length
  S : τ.vars "S" = x.selCount
  mn : τ.vars "mn" = x.m * x.n
  Dc : τ.vars "Dc" = x.dumCount
  N : τ.vars "N" = x.numJobs
  T : τ.vars "T" = x.target
  k1 : τ.vars "k1" = x.k + 1
  MJ : τ.arrs "MJ" = fstArr z.length x.ML
  MI : τ.arrs "MI" = sndArr z.length x.ML

/-- The scratch variables of the loops. -/
def tempVars : List String := ["t", "sg", "ee", "st", "el", "fam", "u", "v", "g", "P", "Qv", "c", "d"]

theorem MCtx.frame {z : List ℕ} {x : HRaw} {τ τ' : Env} (h : MCtx z x τ)
    (ha : τ'.arrs = τ.arrs) (hv : ∀ y ∉ tempVars, τ'.vars y = τ.vars y) : MCtx z x τ' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [ha]; exact h.MJ, by rw [ha]; exact h.MI⟩
  · rw [hv "n" (by decide)]; exact h.n
  · rw [hv "m" (by decide)]; exact h.m
  · rw [hv "k" (by decide)]; exact h.k
  · rw [hv "Q" (by decide)]; exact h.Q
  · rw [hv "Lm" (by decide)]; exact h.Lm
  · rw [hv "S" (by decide)]; exact h.S
  · rw [hv "mn" (by decide)]; exact h.mn
  · rw [hv "Dc" (by decide)]; exact h.Dc
  · rw [hv "N" (by decide)]; exact h.N
  · rw [hv "T" (by decide)]; exact h.T
  · rw [hv "k1" (by decide)]; exact h.k1

/-- What the bounds of a run need. -/
structure Big (z : List ℕ) (x : HRaw) (A B : ℕ) : Prop where
  bnd : Bnd A x
  B : A ^ 21 < B
  ML : x.ML.length ≤ z.length

theorem Big.pow {z : List ℕ} {x : HRaw} {A B : ℕ} (h : Big z x A B) {a : ℕ} (ha : a ≤ 21) :
    A ^ a < B := lt_of_le_of_lt (Nat.pow_le_pow_right h.bnd.A1 ha) h.B

/-! ### The slot of a job -/

theorem slot_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (τ : Env) (hc : MCtx z x τ)
    (t : ℕ) (ht : τ.vars "t" = t) (htN : t < x.numJobs) :
    ∃ τ', Run B slotCom τ τ' 80 ∧ τ'.vars "fam" = x.family t ∧ τ'.vars "sg" = x.seg t ∧
      τ'.vars "st" = x.setIdx t ∧ τ'.vars "el" = x.elem t ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      ∀ y ∉ ["sg", "ee", "st", "el", "fam", "u", "v"], τ'.vars y = τ.vars y := by
  have hN := hg.bnd.N_le
  have hB6 := hg.pow (a := 6) (by norm_num)
  have hS := hg.bnd.S_le
  have hS6 : x.selCount ≤ A ^ 6 := monoB hg.bnd.A1 hS (by norm_num)
  have hDc6 : x.dumCount ≤ A ^ 6 := monoB hg.bnd.A1 hg.bnd.Dc_le (by norm_num)
  have hmn6 : x.m * x.n ≤ A ^ 6 := monoB hg.bnd.A1 hg.bnd.mn_le (by norm_num)
  have hn6 : x.n ≤ A ^ 6 := monoB hg.bnd.A1 (selfB hg.bnd.n) (by norm_num)
  have hl6 : x.ML.length ≤ A ^ 6 := monoB hg.bnd.A1 (selfB hg.bnd.len) (by norm_num)
  have hA6 : A ≤ A ^ 6 := monoB hg.bnd.A1 (selfB (le_refl A)) (by norm_num)
  have hA5 : 5 ≤ A ^ 6 := le_trans hg.bnd.A5 hA6
  have hc0 : (Cond.lt (V "t") (V "S")).evalB B τ = some (decide (t < x.selCount)) :=
    evalB_condLt (ev_var ht (by omega)) (ev_var hc.S (by omega))
  have hfr : ∀ τ' : Env, ∀ y ∉ ["sg", "ee", "st", "el", "fam", "u", "v"], ∀ (a : String) (v : ℕ),
      a ∈ ["sg", "ee", "st", "el", "fam", "u", "v"] → (τ'.setVar a v).vars y = τ'.vars y :=
    fun τ' y hy a v ha => by
      simp only [Env.setVar]; rw [if_neg]; rintro rfl; exact hy ha
  by_cases hsel : t < x.selCount
  · have hl : 0 < x.ML.length := by
      rcases Nat.eq_zero_or_pos x.ML.length with h0 | h0
      · simp [HRaw.selCount, h0] at hsel
      · exact h0
    set L := x.ML.length with hL
    have r1 := Run.assign (x := "sg") (B := B) (σ := τ) (ev_div (ev_var ht (by omega))
      (ev_var hc.Lm (by omega)))
    set τ1 := τ.setVar "sg" (t / L) with hτ1
    have hdm := Nat.div_mul_le_self t L
    have r2 := Run.assign (x := "ee") (B := B) (σ := τ1)
      (ev_sub (ev_var (x := "t") (v := t) (by simp [hτ1, Env.setVar, ht]) (by omega))
        (ev_mul (ev_var (x := "sg") (v := t / L) (by simp [hτ1, Env.setVar]) (by
            have := Nat.div_le_self t L; omega))
          (ev_var (x := "Lm") (v := L) (by simp [hτ1, Env.setVar, hc.Lm, hL]) (by omega)) (by omega)))
    have hee : t - t / L * L = t % L := by rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]
    set τ2 := τ1.setVar "ee" (t - t / L * L) with hτ2
    have hlt : t % L < L := Nat.mod_lt _ hl
    have hmem := Bnd.mem_ML (x := x) (t := t) hl
    have hf := hg.bnd.fst _ hmem
    have hs := hg.bnd.snd _ hmem
    rw [← hL] at hf hs
    have r3 := Run.assign (x := "st") (B := B) (σ := τ2)
      (evalB_get (ev_var (x := "ee") (v := t % L) (by simp [hτ2, Env.setVar, hee]) (by omega))
        (by simp only [hτ2, hτ1, Env.setVar]; rw [hc.MJ]; unfold fstArr
            exact getElem?_arrOf _ (by have := hg.ML; omega)) (by omega))
    set τ3 := τ2.setVar "st" (x.ML.getD (t % L) (0, 0)).1 with hτ3
    have r4 := Run.assign (x := "el") (B := B) (σ := τ3)
      (evalB_get (ev_var (x := "ee") (v := t % L) (by simp [hτ3, hτ2, Env.setVar, hee]) (by omega))
        (by simp only [hτ3, hτ2, hτ1, Env.setVar]; rw [hc.MI]; unfold sndArr
            exact getElem?_arrOf _ (by have := hg.ML; omega)) (by omega))
    set τ4 := τ3.setVar "el" (x.ML.getD (t % L) (0, 0)).2 with hτ4
    have r5 := Run.assign (x := "fam") (B := B) (σ := τ4) (ev_lit (n := 0) (by omega))
    have hsl : x.slot t = (0, t / L, (x.ML.getD (t % L) (0, 0)).1, (x.ML.getD (t % L) (0, 0)).2) := by
      unfold HRaw.slot; rw [if_pos hsel]
    refine ⟨_, (Run.ite_true (by rw [hc0]; exact dtrue hsel)
      (r1.seq (r2.seq (r3.seq (r4.seq r5))))).mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Env.setVar, HRaw.family, hsl]
    · simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, HRaw.seg, hsl]
    · simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, HRaw.setIdx, hsl]
    · simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, HRaw.elem, hsl]
    · simp [hτ4, hτ3, hτ2, hτ1, Env.setVar]
    · simp [hτ4, hτ3, hτ2, hτ1, Env.setVar]
    · intro y hy
      rw [hfr _ y hy "fam" _ (by simp), hfr _ y hy "el" _ (by simp), hfr _ y hy "st" _ (by simp),
        hfr _ y hy "ee" _ (by simp), hfr _ y hy "sg" _ (by simp)]
  · set u := t - x.selCount with hu
    have r1 := Run.assign (x := "u") (B := B) (σ := τ) (ev_sub (ev_var ht (by omega))
      (ev_var hc.S (by omega)))
    set τ1 := τ.setVar "u" u with hτ1
    have hc1 : (Cond.lt (V "u") (V "Dc")).evalB B τ1 = some (decide (u < x.dumCount)) :=
      evalB_condLt (ev_var (x := "u") (v := u) (by simp [hτ1, Env.setVar]) (by omega))
        (ev_var (x := "Dc") (v := x.dumCount) (by simp [hτ1, Env.setVar, hc.Dc]) (by omega))
    set v := if u < x.dumCount then u else u - x.dumCount with hv
    set f := if u < x.dumCount then 1 else 2 with hf
    have hvu : v ≤ u := by rw [hv]; split_ifs <;> omega
    obtain ⟨τ2, r2, hτ2v, hτ2f, hτ2a, hτ2o, hτ2r⟩ : ∃ τ2, Run B
        (.ite (.lt (V "u") (V "Dc")) (.seq (.assign "v" (V "u")) (.assign "fam" (.lit 1)))
          (.seq (.assign "v" (sub (V "u") (V "Dc"))) (.assign "fam" (.lit 2)))) τ1 τ2 20 ∧
        τ2.vars "v" = v ∧ τ2.vars "fam" = f ∧ τ2.arrs = τ1.arrs ∧ τ2.out = τ1.out ∧
        ∀ y ∉ ["sg", "ee", "st", "el", "fam", "u", "v"], τ2.vars y = τ1.vars y := by
      by_cases hd : u < x.dumCount
      · have a1 := Run.assign (x := "v") (B := B) (σ := τ1)
          (ev_var (x := "u") (v := u) (by simp [hτ1, Env.setVar]) (by omega))
        have a2 := Run.assign (x := "fam") (B := B) (σ := τ1.setVar "v" u) (ev_lit (n := 1) (by omega))
        refine ⟨_, (Run.ite_true (by rw [hc1]; exact dtrue hd) (a1.seq a2)).mono (by simp),
          by simp [Env.setVar, hv, hd], by simp [Env.setVar, hf, hd], rfl, rfl, fun y hy => ?_⟩
        rw [hfr _ y hy "fam" _ (by simp), hfr _ y hy "v" _ (by simp)]
      · have a1 := Run.assign (x := "v") (B := B) (σ := τ1)
          (ev_sub (ev_var (x := "u") (v := u) (by simp [hτ1, Env.setVar]) (by omega))
            (ev_var (x := "Dc") (v := x.dumCount) (by simp [hτ1, Env.setVar, hc.Dc]) (by omega)))
        have a2 := Run.assign (x := "fam") (B := B) (σ := τ1.setVar "v" (u - x.dumCount))
          (ev_lit (n := 2) (by omega))
        refine ⟨_, (Run.ite_false (by rw [hc1]; exact dfalse hd) (a1.seq a2)).mono (by simp),
          by simp [Env.setVar, hv, hd], by simp [Env.setVar, hf, hd], rfl, rfl, fun y hy => ?_⟩
        rw [hfr _ y hy "fam" _ (by simp), hfr _ y hy "v" _ (by simp)]
    have hτ2mn : τ2.vars "mn" = x.m * x.n := by
      rw [hτ2r "mn" (by decide)]; simp [hτ1, Env.setVar, hc.mn]
    have hτ2n : τ2.vars "n" = x.n := by
      rw [hτ2r "n" (by decide)]; simp [hτ1, Env.setVar, hc.n]
    set mn := x.m * x.n with hmn
    have r3 := Run.assign (x := "sg") (B := B) (σ := τ2)
      (ev_div (ev_var hτ2v (by omega)) (ev_var hτ2mn (by omega)))
    set τ3 := τ2.setVar "sg" (v / mn) with hτ3
    have hdm := Nat.div_mul_le_self v mn
    have r4 := Run.assign (x := "st") (B := B) (σ := τ3)
      (ev_div (ev_sub (ev_var (x := "v") (v := v) (by simp [hτ3, Env.setVar, hτ2v]) (by omega))
        (ev_mul (ev_var (x := "sg") (v := v / mn) (by simp [hτ3, Env.setVar])
          (by have := Nat.div_le_self v mn; omega))
          (ev_var (x := "mn") (v := mn) (by simp [hτ3, Env.setVar, hτ2mn]) (by omega)) (by omega)))
        (ev_var (x := "n") (v := x.n) (by simp [hτ3, Env.setVar, hτ2n]) (by omega)))
    set τ4 := τ3.setVar "st" ((v - v / mn * mn) / x.n) with hτ4
    have hdn := Nat.div_mul_le_self v x.n
    have r5 := Run.assign (x := "el") (B := B) (σ := τ4)
      (ev_sub (ev_var (x := "v") (v := v) (by simp [hτ4, hτ3, Env.setVar, hτ2v]) (by omega))
        (ev_mul (ev_div (ev_var (x := "v") (v := v) (by simp [hτ4, hτ3, Env.setVar, hτ2v]) (by omega))
          (ev_var (x := "n") (v := x.n) (by simp [hτ4, hτ3, Env.setVar, hτ2n]) (by omega)))
          (ev_var (x := "n") (v := x.n) (by simp [hτ4, hτ3, Env.setVar, hτ2n]) (by omega))
          (by omega)))
    have hsl : x.slot t = (f, v / mn, v % mn / x.n, v % x.n) := by
      unfold HRaw.slot; rw [if_neg hsel]
    have e1 : v - v / mn * mn = v % mn := by rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]
    have e2 : v - v / x.n * x.n = v % x.n := by rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]
    refine ⟨_, (Run.ite_false (by rw [hc0]; exact dfalse hsel)
      (r1.seq (r2.seq (r3.seq (r4.seq r5))))).mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hτ4, hτ3, Env.setVar, HRaw.family, hsl, hτ2f]
    · simp [hτ4, hτ3, Env.setVar, HRaw.seg, hsl]
    · simp [hτ4, hτ3, Env.setVar, HRaw.setIdx, hsl, e1]
    · simp [hτ4, hτ3, Env.setVar, HRaw.elem, hsl, e2]
    · simp [hτ4, hτ3, Env.setVar, hτ2a, hτ1]
    · simp [hτ4, hτ3, Env.setVar, hτ2o, hτ1]
    · intro y hy
      rw [hfr _ y hy "el" _ (by simp), hfr _ y hy "st" _ (by simp), hfr _ y hy "sg" _ (by simp),
        hτ2r y hy, hfr _ y hy "u" _ (by simp)]

/-! ### The processing times and the due date -/

theorem gCom_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (τ : Env) (hc : MCtx z x τ)
    (t : ℕ) (htN : t < x.numJobs) (hsg : τ.vars "sg" = x.seg t) (hst : τ.vars "st" = x.setIdx t) :
    Run B gCom τ (τ.setVar "g" (x.g (x.seg t) (x.setIdx t))) 10 := by
  obtain ⟨h1, h2, -⟩ := hg.bnd.slot_le htN
  have hg8 := hg.bnd.g_le htN
  have hB8 := hg.pow (a := 8) (by norm_num)
  have hsm : x.seg t * x.m ≤ A ^ 7 := by have := mulB h1 (selfB hg.bnd.m); simpa using this
  have hA7 : A ^ 7 ≤ A ^ 8 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hgv : x.seg t * x.m + x.setIdx t + 1 = x.g (x.seg t) (x.setIdx t) := by
    unfold HRaw.g; ring
  have hA6 : A ^ 6 ≤ A ^ 8 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hgv' : x.seg t * x.m + x.setIdx t + 1 ≤ A ^ 8 := by rw [hgv]; exact hg8
  have := Run.assign (x := "g") (B := B) (σ := τ)
    (ev_add (ev_add (ev_mul (ev_var hsg (by omega)) (ev_var hc.m (by
        have := hg.bnd.m; have : A ≤ A ^ 8 := monoB hg.bnd.A1 (selfB le_rfl) (by norm_num); omega))
      (by omega)) (ev_var hst (by omega)) (by omega)) (ev_lit (n := 1) (by omega)) (by omega))
  rw [hgv] at this
  exact this.mono (by simp)

theorem pqCom_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (τ : Env) (hc : MCtx z x τ)
    (t : ℕ) (htN : t < x.numJobs) (hfam : τ.vars "fam" = x.family t)
    (hgv : τ.vars "g" = x.g (x.seg t) (x.setIdx t)) :
    ∃ τ', Run B pqCom τ τ' 40 ∧ τ'.vars "P" = x.jp t ∧ τ'.vars "Qv" = x.jq t ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ ∀ y ∉ ["P", "Qv"], τ'.vars y = τ.vars y := by
  set gg := x.g (x.seg t) (x.setIdx t) with hgg
  have hg8 := hg.bnd.g_le htN
  have hQ := hg.bnd.Q_le
  have hB := hg.pow (a := 12) (by norm_num)
  have e1 : gg * (x.n + 1) ≤ A ^ 10 := by
    have := mulB hg8 (addB hg.bnd.A2 (selfB hg.bnd.n) (oneB hg.bnd.A1 0) (by norm_num)
      (show 0 < 2 by norm_num)); simpa using this
  have e2 : 2 * gg + 1 ≤ A ^ 9 := by
    have h9 : A ^ 9 = A * A ^ 8 := by ring
    have h1 := oneB hg.bnd.A1 8
    have h5 : 5 * A ^ 8 ≤ A * A ^ 8 := Nat.mul_le_mul_right _ hg.bnd.A5
    omega
  have e3 : (2 * gg + 1) * x.Q ≤ A ^ 12 := by have := mulB e2 hQ; simpa using this
  have e4 : gg * x.Q ≤ A ^ 11 := by have := mulB hg8 hQ; simpa using this
  have e5 : (gg + 1) * x.Q ≤ A ^ 12 := by
    have := mulB (show gg + 1 ≤ A ^ 9 by omega) hQ; simpa using this
  have hA11 : A ^ 11 ≤ A ^ 12 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA10 : A ^ 10 ≤ A ^ 12 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA9 : A ^ 9 ≤ A ^ 12 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA8 : A ^ 8 ≤ A ^ 12 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA3 : A ^ 3 ≤ A ^ 12 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hn12 : x.n ≤ A ^ 12 := monoB hg.bnd.A1 (selfB hg.bnd.n) (by norm_num)
  have hn1 : x.n + 1 ≤ A ^ 12 := monoB hg.bnd.A1 (addB hg.bnd.A2 (selfB hg.bnd.n) (oneB hg.bnd.A1 0)
    (show 1 < 2 by norm_num) (show 0 < 2 by norm_num)) (by norm_num)
  have hA5 : 5 ≤ A ^ 12 := le_trans hg.bnd.A5 (monoB hg.bnd.A1 (selfB le_rfl) (by norm_num))
  have hfr : ∀ τ' : Env, ∀ y ∉ ["P", "Qv"], ∀ (a : String) (v : ℕ),
      a ∈ ["P", "Qv"] → (τ'.setVar a v).vars y = τ'.vars y :=
    fun τ' y hy a v ha => by simp only [Env.setVar]; rw [if_neg]; rintro rfl; exact hy ha
  have hfam2 : x.family t ≤ 2 := by
    unfold HRaw.family HRaw.slot
    by_cases h1 : t < x.selCount
    · simp [h1]
    · simp only [h1, if_false]; split_ifs <;> omega
  have hc0 : (Cond.eq (V "fam") (.lit 0)).evalB B τ = some (x.family t == 0) :=
    evalB_condEq (ev_var hfam (by omega)) (ev_lit (by omega))
  by_cases h0 : x.family t = 0
  · have r1 := Run.assign (x := "P") (B := B) (σ := τ) (ev_lit (n := 0) (by omega))
    have r2 := Run.assign (x := "Qv") (B := B) (σ := τ.setVar "P" 0)
      (ev_mul (ev_add (ev_mul (ev_lit (n := 2) (by omega))
        (ev_var (x := "g") (v := gg) (by simp [Env.setVar, hgv]) (by omega)) (by omega))
        (ev_lit (n := 1) (by omega)) (by omega))
        (ev_var (x := "Q") (v := x.Q) (by simp [Env.setVar, hc.Q]) (by omega)) (by omega))
    refine ⟨_, (Run.ite_true (by rw [hc0]; exact btrue h0) (r1.seq r2)).mono (by simp),
      by simp [Env.setVar, HRaw.jp, h0], by simp [Env.setVar, HRaw.jq, h0, hgg], rfl, rfl,
      fun y hy => by rw [hfr _ y hy "Qv" _ (by simp), hfr _ y hy "P" _ (by simp)]⟩
  · have r1 := Run.assign (x := "P") (B := B) (σ := τ)
      (ev_mul (ev_var hgv (by omega)) (ev_add (ev_var hc.n (by omega)) (ev_lit (n := 1) (by omega))
        (by omega)) (by omega))
    set τ1 := τ.setVar "P" (gg * (x.n + 1)) with hτ1
    have hc1 : (Cond.eq (V "fam") (.lit 1)).evalB B τ1 = some (x.family t == 1) :=
      evalB_condEq (ev_var (x := "fam") (v := x.family t) (by simp [hτ1, Env.setVar, hfam])
        (by omega)) (ev_lit (by omega))
    have hgv1 : τ1.vars "g" = gg := by simp [hτ1, Env.setVar, hgv]
    have hQ1 : τ1.vars "Q" = x.Q := by simp [hτ1, Env.setVar, hc.Q]
    by_cases h1 : x.family t = 1
    · have r2 := Run.assign (x := "Qv") (B := B) (σ := τ1)
        (ev_mul (ev_var hgv1 (by omega)) (ev_var hQ1 (by omega)) (by omega))
      refine ⟨_, (Run.ite_false (by rw [hc0]; exact bfalse h0)
        (r1.seq (Run.ite_true (by rw [hc1]; exact btrue h1) r2))).mono (by simp),
        by simp [hτ1, Env.setVar, HRaw.jp, h0, hgg], by simp [Env.setVar, HRaw.jq, h1, hgg], rfl, rfl,
        fun y hy => by rw [hfr _ y hy "Qv" _ (by simp), hfr _ y hy "P" _ (by simp)]⟩
    · have r2 := Run.assign (x := "Qv") (B := B) (σ := τ1)
        (ev_mul (ev_add (ev_var hgv1 (by omega)) (ev_lit (n := 1) (by omega)) (by omega))
          (ev_var hQ1 (by omega)) (by omega))
      refine ⟨_, (Run.ite_false (by rw [hc0]; exact bfalse h0)
        (r1.seq (Run.ite_false (by rw [hc1]; exact bfalse h1) r2))).mono (by simp),
        by simp [hτ1, Env.setVar, HRaw.jp, h0, hgg], by simp [Env.setVar, HRaw.jq, h0, h1, hgg], rfl, rfl,
        fun y hy => by rw [hfr _ y hy "Qv" _ (by simp), hfr _ y hy "P" _ (by simp)]⟩

theorem dCom_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (τ : Env) (hc : MCtx z x τ)
    (t : ℕ) (htN : t < x.numJobs) (hfam : τ.vars "fam" = x.family t)
    (hgv : τ.vars "g" = x.g (x.seg t) (x.setIdx t)) (hel : τ.vars "el" = x.elem t) :
    Run B dCom τ (τ.setVar "d" (x.jd t)) 40 := by
  set gg := x.g (x.seg t) (x.setIdx t) with hgg
  have hg8 := hg.bnd.g_le htN
  have hQ := hg.bnd.Q_le
  obtain ⟨-, -, he6⟩ := hg.bnd.slot_le htN
  have hB := hg.B
  have e1 : gg * gg ≤ A ^ 16 := by have := mulB hg8 hg8; simpa using this
  have e2 : gg * gg * x.Q ≤ A ^ 19 := by have := mulB e1 hQ; simpa using this
  have e3 : gg * x.Q ≤ A ^ 11 := by have := mulB hg8 hQ; simpa using this
  have e4 : 2 * gg + 1 ≤ A ^ 9 := by
    have h9 : A ^ 9 = A * A ^ 8 := by ring
    have h1 := oneB hg.bnd.A1 8
    have h5 : 5 * A ^ 8 ≤ A * A ^ 8 := Nat.mul_le_mul_right _ hg.bnd.A5
    omega
  have e5 : (2 * gg + 1) * x.Q ≤ A ^ 12 := by have := mulB e4 hQ; simpa using this
  have s1 : gg * gg * x.Q + gg * x.Q ≤ A ^ 20 := addB hg.bnd.A2 e2 e3 (by norm_num) (by norm_num)
  have s2 : gg * gg * x.Q + (2 * gg + 1) * x.Q ≤ A ^ 20 :=
    addB hg.bnd.A2 e2 e5 (by norm_num) (by norm_num)
  have s3 : ∀ w, w ≤ A ^ 20 → w + x.elem t + 1 ≤ A ^ 21 := fun w hw => by
    have := addB (c := 21) hg.bnd.A2 hw (show x.elem t + 1 ≤ A ^ 7 from
      addB hg.bnd.A2 he6 (oneB hg.bnd.A1 0) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
    omega
  have t1 := s3 _ s1
  have t2 := s3 _ s2
  have hA16 : A ^ 16 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA19 : A ^ 19 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA12 : A ^ 12 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA11 : A ^ 11 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA9 : A ^ 9 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA8 : A ^ 8 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA3 : A ^ 3 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA6 : A ^ 6 ≤ A ^ 20 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA20 : A ^ 20 ≤ A ^ 21 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
  have hA5 : 5 ≤ A ^ 20 := le_trans hg.bnd.A5 (monoB hg.bnd.A1 (selfB le_rfl) (by norm_num))
  have hfam2 : x.family t ≤ 2 := by
    unfold HRaw.family HRaw.slot
    by_cases h1 : t < x.selCount
    · simp [h1]
    · simp only [h1, if_false]; split_ifs <;> omega
  have hc0 : (Cond.eq (V "fam") (.lit 1)).evalB B τ = some (x.family t == 1) :=
    evalB_condEq (ev_var hfam (by omega)) (ev_lit (by omega))
  have hG : x.G (x.seg t) (x.setIdx t) = gg * gg * x.Q := by unfold HRaw.G; rw [← hgg]; ring
  have egg := ev_mul (B := B) (σ := τ) (ev_var hgv (by omega)) (ev_var hgv (by omega)) (by omega)
  have eggQ := ev_mul (B := B) (σ := τ) egg (ev_var hc.Q (by omega)) (by omega)
  by_cases h1 : x.family t = 1
  · have ev := ev_add (B := B) (σ := τ) (ev_add (ev_add eggQ (ev_mul (ev_var hgv (by omega))
      (ev_var hc.Q (by omega)) (by omega)) (by omega)) (ev_var hel (by omega)) (by omega))
      (ev_lit (n := 1) (by omega)) (by omega)
    have hd : gg * gg * x.Q + gg * x.Q + x.elem t + 1 = x.jd t := by
      unfold HRaw.jd; rw [if_pos h1, hG]; ring
    have r := Run.assign (x := "d") ev
    rw [hd] at r
    exact (Run.ite_true (by rw [hc0]; exact btrue h1) r).mono (by simp)
  · have ev := ev_add (B := B) (σ := τ) (ev_add (ev_add eggQ (ev_mul (ev_add (ev_mul
      (ev_lit (n := 2) (by omega)) (ev_var hgv (by omega)) (by omega)) (ev_lit (n := 1) (by omega))
      (by omega)) (ev_var hc.Q (by omega)) (by omega)) (by omega)) (ev_var hel (by omega)) (by omega))
      (ev_lit (n := 1) (by omega)) (by omega)
    have hd : gg * gg * x.Q + (2 * gg + 1) * x.Q + x.elem t + 1 = x.jd t := by
      unfold HRaw.jd; rw [if_neg h1, hG]; ring
    have r := Run.assign (x := "d") ev
    rw [hd] at r
    exact (Run.ite_false (by rw [hc0]; exact bfalse h1) r).mono (by simp)

/-! ### Loops that write -/

theorem run_loopOut {B : ℕ} (x m : String) (c : Com) (N Kb : ℕ) (f : ℕ → List ℕ) (hNB : N < B)
    (Q : ℕ → Env → Prop) (σ : Env) (hm : σ.vars m = N) (hxm : m ≠ x)
    (hbody : ∀ k < N, ∀ τ, τ.vars x = k → τ.vars m = N → Q k τ →
      ∃ τ', Run B c τ τ' Kb ∧ τ'.vars x = k + 1 ∧ τ'.vars m = N ∧ Q (k + 1) τ' ∧
        τ'.out = τ.out ++ f k)
    (h0 : Q 0 (σ.setVar x 0)) :
    ∃ σ', Run B (forLoop x m c) σ σ' ((Kb + 4) * N + 6) ∧ Q N σ' ∧
      σ'.out = σ.out ++ (List.range N).flatMap f := by
  obtain ⟨σ', hr, -, -, hQ, hout⟩ := run_forLoop (B := B) x m c N Kb hNB
    (fun k τ => τ.vars x = k ∧ τ.vars m = N ∧ Q k τ ∧
      τ.out = σ.out ++ (List.range k).flatMap f)
    (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hj, hnn, hq, ho⟩ => by
      obtain ⟨τ', hr, hj', hn', hq', ho'⟩ := hbody k hk τ hj hnn hq
      exact ⟨τ', hr, hj', hn', hq', by rw [ho', ho, List.range_succ, List.flatMap_append]; simp⟩)
    (σ := σ) ⟨by simp [Env.setVar], by simp [Env.setVar, hxm, hm], h0, by simp [Env.setVar]⟩
  exact ⟨σ', hr, hQ, hout⟩

theorem flatMap_rep (val : ℕ) : ∀ N, (List.range N).flatMap (fun _ => [val]) = List.replicate N val
  | 0 => rfl
  | N + 1 => by rw [List.range_succ, List.flatMap_append, flatMap_rep val N, List.replicate_succ']; rfl

/-- A loop writing one value per round. -/
theorem run_repW {B : ℕ} (cnt : String) (w : String) (N val : ℕ) (σ : Env) (hcnt : σ.vars cnt = N)
    (hw : σ.vars w = val) (hNB : N + 1 < B) (hvB : val < B) (h1 : cnt ≠ "c") (h2 : w ≠ "c") :
    ∃ σ', Run B (forLoop "c" cnt (.seq (.write (V w)) (incr "c"))) σ σ' (10 * N + 6) ∧
      σ'.out = σ.out ++ List.replicate N val ∧ σ'.arrs = σ.arrs ∧
      ∀ y, y ≠ "c" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, ⟨ha, hv⟩, ho⟩ := run_loopOut (B := B) "c" cnt _ N 6 (fun _ => [val]) (by omega)
    (fun _ τ => τ.arrs = σ.arrs ∧ ∀ y, y ≠ "c" → τ.vars y = σ.vars y) σ hcnt h1
    (fun k hk τ hk' _ ⟨ha, hv⟩ => by
      have r1 := Run.write (B := B) (σ := τ) (ev_var (x := w) (v := val) (by rw [hv w h2, hw]) hvB)
      have r2 := Run.assign (x := "c") (B := B) (σ := { τ with out := τ.out ++ [val] })
        (ev_add (ev_var (x := "c") (v := k) (by simpa using hk') (by omega)) (ev_lit (n := 1) (by omega))
          (by omega))
      refine ⟨_, (r1.seq r2).mono (by simp), by simp [Env.setVar],
        by simp [Env.setVar, h1]; rw [hv cnt h1, hcnt], ⟨by simp [Env.setVar, ha],
        fun y hy => by simp [Env.setVar, hy]; exact hv y hy⟩, by simp [Env.setVar]⟩)
    ⟨by simp [Env.setVar], fun y hy => by simp [Env.setVar, hy]⟩
  refine ⟨σ', r.mono (by omega), by rw [ho, flatMap_rep], ha,
    fun y hy => by rw [hv y hy]⟩

/-! ### A record -/

theorem flat_machList (k : ℕ) : Lax434175.StandardReading.flat (machList k) =
    (k + 1) :: [2, 0, 0] ++ (List.range k).flatMap fun c => [2, 1, c + 1] := by
  simp [Lax434175.StandardReading.flat, machList, List.flatMap_map]

theorem recJ_eq (k p q : ℕ) : (recJ k p q).length :: recJ k p q =
    [5 * k + 27, 2] ++ List.replicate (k + 1) p ++ List.replicate (k + 1) q ++ [0, k + 1] ++
      [2, 0, 0] ++ ((List.range k).flatMap fun c => [2, 1, c + 1]) ++ recTail := by
  have hl : ((List.range k).flatMap fun c => [2, 1, c + 1]).length = 3 * k := by
    rw [List.length_flatMap]; simp [List.sum_replicate, Nat.mul_comm]
  have e : recJ k p q = [2] ++ List.replicate (k + 1) p ++ List.replicate (k + 1) q ++ [0, k + 1] ++
      [2, 0, 0] ++ ((List.range k).flatMap fun c => [2, 1, c + 1]) ++ recTail := by
    simp [recJ, flat_machList, recTail]
  have hlen : (recJ k p q).length = 5 * k + 27 := by
    rw [e]
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil, hl,
      recTail, Lax434175.StandardReading.flat, transList]
    simp; ring
  rw [hlen, e]
  simp

theorem recCom_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (τ : Env) (hc : MCtx z x τ)
    (p q : ℕ) (hP : τ.vars "P" = p) (hQv : τ.vars "Qv" = q) (hp : p < B) (hq : q < B) :
    ∃ τ', Run B recCom τ τ' (40 * x.k + 200) ∧
      τ'.out = τ.out ++ ((recJ x.k p q).length :: recJ x.k p q) ∧ τ'.arrs = τ.arrs ∧
      ∀ y, y ≠ "c" → τ'.vars y = τ.vars y := by
  have hk := hg.bnd.k
  have hB2 := hg.pow (a := 2) (by norm_num)
  have hB3 := hg.pow (a := 3) (by norm_num)
  have hAA : 5 * x.k + 27 < B := by
    have e3 : A ^ 3 = A * A * A := by ring
    have := hg.bnd.A5
    have : 25 * A ≤ A * A * A := by nlinarith
    omega
  have r1 := Run.write (B := B) (σ := τ) (ev_add (ev_mul (ev_lit (n := 5) (by omega))
    (ev_var hc.k (by omega)) (by omega)) (ev_lit (n := 27) (by omega)) (by omega))
  set τ1 := { τ with out := τ.out ++ [5 * x.k + 27] } with hτ1
  have r2 := Run.write (B := B) (σ := τ1) (ev_lit (n := 2) (by omega))
  set τ2 := { τ1 with out := τ1.out ++ [2] } with hτ2
  obtain ⟨τ3, r3, ho3, ha3, hv3⟩ := run_repW (B := B) "k1" "P" (x.k + 1) p τ2
    (by simp [hτ2, hτ1, hc.k1]) (by simp [hτ2, hτ1, hP]) (by omega) hp (by decide) (by decide)
  obtain ⟨τ4, r4, ho4, ha4, hv4⟩ := run_repW (B := B) "k1" "Qv" (x.k + 1) q τ3
    (by rw [hv3 "k1" (by decide)]; simp [hτ2, hτ1, hc.k1])
    (by rw [hv3 "Qv" (by decide)]; simp [hτ2, hτ1, hQv]) (by omega) hq (by decide) (by decide)
  have r5 := Run.write (B := B) (σ := τ4) (ev_lit (n := 0) (by omega))
  set τ5 := { τ4 with out := τ4.out ++ [0] } with hτ5
  have hk1 : τ5.vars "k1" = x.k + 1 := by
    simp only [hτ5]; rw [hv4 "k1" (by decide), hv3 "k1" (by decide)]; simp [hτ2, hτ1, hc.k1]
  have r6 := Run.write (B := B) (σ := τ5) (ev_var hk1 (by omega))
  set τ6 := { τ5 with out := τ5.out ++ [x.k + 1] } with hτ6
  have r7 := run_writeList (B := B) τ6 [2, 0, 0] (by simp; omega)
  set τ7 := { τ6 with out := τ6.out ++ [2, 0, 0] } with hτ7
  have hk7 : τ7.vars "k" = x.k := by
    simp only [hτ7, hτ6, hτ5]; rw [hv4 "k" (by decide), hv3 "k" (by decide)]; simp [hτ2, hτ1, hc.k]
  obtain ⟨τ8, r8, ⟨ha8, hv8⟩, ho8⟩ := run_loopOut (B := B) "c" "k" _ x.k 14
    (fun c => [2, 1, c + 1]) (by omega)
    (fun _ σ => σ.arrs = τ7.arrs ∧ ∀ y, y ≠ "c" → σ.vars y = τ7.vars y) τ7 hk7 (by decide)
    (fun c hc' σ hcv _ ⟨ha, hv⟩ => by
      have w1 := run_writeList (B := B) σ [2, 1] (by simp; omega)
      have w2 := Run.write (B := B) (σ := { σ with out := σ.out ++ [2, 1] })
        (ev_add (ev_var (x := "c") (v := c) (by simpa using hcv) (by omega)) (ev_lit (n := 1) (by omega))
          (by omega))
      have w3 := Run.assign (x := "c") (B := B)
        (σ := { { σ with out := σ.out ++ [2, 1] } with out := σ.out ++ [2, 1] ++ [c + 1] })
        (ev_add (ev_var (x := "c") (v := c) (by simpa using hcv) (by omega)) (ev_lit (n := 1) (by omega))
          (by omega))
      refine ⟨_, (w1.seq (w2.seq w3)).mono (by simp), by simp [Env.setVar],
        by simp [Env.setVar]; rw [hv "k" (by decide), hk7], ⟨by simp [Env.setVar, ha],
        fun y hy => by simp [Env.setVar, hy]; exact hv y hy⟩, by simp [Env.setVar]⟩)
    ⟨by simp [Env.setVar], fun y hy => by simp [Env.setVar, hy]⟩
  have hrt : ∀ v ∈ recTail, v < B := by
    intro v hv
    simp [recTail, Lax434175.StandardReading.flat, transList] at hv
    omega
  have r9 := run_writeList (B := B) τ8 recTail hrt
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono ?_,
    ?_, ?_, fun y hy => ?_⟩
  · simp only [List.length_cons, List.length_nil, size_add, size_mul, size_lit, size_var, recTail,
      Lax434175.StandardReading.flat, transList, List.length_append]
    simp; omega
  · rw [recJ_eq]
    simp only [ho8, hτ7, hτ6, hτ5, ho4, ho3, hτ2, hτ1]
    simp
  · simp only [ha8, hτ7, hτ6, hτ5, ha4, ha3, hτ2, hτ1]
  · simp only
    rw [hv8 y hy]
    simp only [hτ7, hτ6, hτ5]
    rw [hv4 y hy, hv3 y hy]

/-! ### The loop bodies -/

theorem incrT_run {B : ℕ} (τ : Env) (t : ℕ) (ht : τ.vars "t" = t) (hB : t + 1 < B) :
    Run B (incr "t") τ (τ.setVar "t" (t + 1)) 4 :=
  (Run.assign (B := B) (σ := τ) (ev_add (ev_var ht (by omega)) (ev_lit (n := 1) (by omega)) hB)).mono
    (by simp)

theorem recBody_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (τ : Env) (hc : MCtx z x τ)
    (t : ℕ) (ht : τ.vars "t" = t) (htN : t < x.numJobs) :
    ∃ τ', Run B recBody τ τ' (40 * x.k + 400) ∧ τ'.vars "t" = t + 1 ∧ τ'.out = τ.out ++ x.recW t ∧
      τ'.arrs = τ.arrs ∧ ∀ y ∉ tempVars, τ'.vars y = τ.vars y := by
  have hN := hg.bnd.N_le
  have hB6 := hg.pow (a := 6) (by norm_num)
  have hB12 := hg.pow (a := 12) (by norm_num)
  obtain ⟨τ1, r1, hfam, hsg, hst, hel, ha1, ho1, hv1⟩ := slot_run hg τ hc t ht htN
  have hc1 : MCtx z x τ1 := hc.frame ha1 fun y hy => hv1 y (by
    intro h; apply hy; simp only [tempVars, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
  have r2 := gCom_run hg τ1 hc1 t htN hsg hst
  set τ2 := τ1.setVar "g" (x.g (x.seg t) (x.setIdx t)) with hτ2
  have hc2 : MCtx z x τ2 := hc1.frame rfl fun y hy => by
    simp only [hτ2, Env.setVar]; rw [if_neg]; rintro rfl; exact hy (by decide)
  obtain ⟨τ3, r3, hP, hQv, ha3, ho3, hv3⟩ := pqCom_run hg τ2 hc2 t htN
    (by simp [hτ2, Env.setVar, hfam]) (by simp [hτ2, Env.setVar])
  have hc3 : MCtx z x τ3 := hc2.frame ha3 fun y hy => hv3 y (by
    intro h; apply hy; simp only [tempVars, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
  have hjp : x.jp t ≤ A ^ 12 := by
    have hg8 := hg.bnd.g_le htN
    unfold HRaw.jp; split_ifs
    · exact Nat.zero_le _
    · have := mulB hg8 (show x.n + 1 ≤ A ^ 4 from monoB hg.bnd.A1 (addB hg.bnd.A2 (selfB hg.bnd.n)
        (oneB hg.bnd.A1 0) (show 1 < 2 by norm_num) (show 0 < 2 by norm_num)) (by norm_num))
      simpa using this
  have hjq : x.jq t ≤ A ^ 12 := by
    have hg8 := hg.bnd.g_le htN
    have hQ := hg.bnd.Q_le
    have h9 : A ^ 9 = A * A ^ 8 := by ring
    have h1 := oneB hg.bnd.A1 8
    have h5 : 5 * A ^ 8 ≤ A * A ^ 8 := Nat.mul_le_mul_right _ hg.bnd.A5
    have e2 : 2 * x.g (x.seg t) (x.setIdx t) + 1 ≤ A ^ 9 := by omega
    unfold HRaw.jq; split_ifs
    · have := mulB e2 hQ; simpa using this
    · have := mulB (monoB hg.bnd.A1 hg8 (show 8 ≤ 9 by norm_num)) hQ; simpa using this
    · have := mulB (show x.g (x.seg t) (x.setIdx t) + 1 ≤ A ^ 9 by omega) hQ; simpa using this
  obtain ⟨τ4, r4, ho4, ha4, hv4⟩ := recCom_run hg τ3 hc3 _ _ hP hQv (by omega) (by omega)
  have ht4 : τ4.vars "t" = t := by
    rw [hv4 "t" (by decide), hv3 "t" (by decide)]; simp [hτ2, Env.setVar]; rw [hv1 "t" (by decide), ht]
  have r5 := incrT_run (B := B) τ4 t ht4 (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, by simp [Env.setVar], ?_, ?_, ?_⟩
  · omega
  · simp only [Env.setVar]
    rw [ho4, ho3, hτ2]
    simp only [Env.setVar]
    rw [ho1]
    rfl
  · simp only [Env.setVar]; rw [ha4, ha3, hτ2]; simp only [Env.setVar]; rw [ha1]
  · intro y hy
    simp only [tempVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Env.setVar, hy.1, if_false]
    rw [hv4 y hy.2.2.2.2.2.2.2.2.2.2.2.1, hv3 y (by simp; tauto)]
    simp only [hτ2, Env.setVar, hy.2.2.2.2.2.2.2.2.1, if_false]
    exact hv1 y (by simp; tauto)

theorem dueBody_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (τ : Env) (hc : MCtx z x τ)
    (t : ℕ) (ht : τ.vars "t" = t) (htN : t < x.numJobs) :
    ∃ τ', Run B dueBody τ τ' 200 ∧ τ'.vars "t" = t + 1 ∧ τ'.out = τ.out ++ x.dueW t ∧
      τ'.arrs = τ.arrs ∧ ∀ y ∉ tempVars, τ'.vars y = τ.vars y := by
  have hN := hg.bnd.N_le
  have hB6 := hg.pow (a := 6) (by norm_num)
  obtain ⟨τ1, r1, hfam, hsg, hst, hel, ha1, ho1, hv1⟩ := slot_run hg τ hc t ht htN
  have hc1 : MCtx z x τ1 := hc.frame ha1 fun y hy => hv1 y (by
    intro h; apply hy; simp only [tempVars, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
  have r2 := gCom_run hg τ1 hc1 t htN hsg hst
  set τ2 := τ1.setVar "g" (x.g (x.seg t) (x.setIdx t)) with hτ2
  have hc2 : MCtx z x τ2 := hc1.frame rfl fun y hy => by
    simp only [hτ2, Env.setVar]; rw [if_neg]; rintro rfl; exact hy (by decide)
  have r3 := dCom_run hg τ2 hc2 t htN (by simp [hτ2, Env.setVar, hfam]) (by simp [hτ2, Env.setVar])
    (by simp [hτ2, Env.setVar, hel])
  set τ3 := τ2.setVar "d" (x.jd t) with hτ3
  have r4 := run_writeList (B := B) τ3 [0, 1] (by simp; omega)
  set τ4 := { τ3 with out := τ3.out ++ [0, 1] } with hτ4
  have hd : x.jd t < B := by
    -- the bound of the due date, as in `dCom_run`
    have hg8 := hg.bnd.g_le htN
    have hQ := hg.bnd.Q_le
    obtain ⟨-, -, he6⟩ := hg.bnd.slot_le htN
    have e1 : x.g (x.seg t) (x.setIdx t) ^ 2 * x.Q ≤ A ^ 19 := by
      have := mulB (mulB hg8 hg8) hQ; rw [pow_two]; simpa using this
    have h9 : A ^ 9 = A * A ^ 8 := by ring
    have h1 := oneB hg.bnd.A1 8
    have h5 : 5 * A ^ 8 ≤ A * A ^ 8 := Nat.mul_le_mul_right _ hg.bnd.A5
    have e2 : 2 * x.g (x.seg t) (x.setIdx t) + 1 ≤ A ^ 9 := by omega
    have e3 := mulB e2 hQ
    have e4 := mulB hg8 hQ
    have e5 : x.elem t + 1 ≤ A ^ 7 := addB hg.bnd.A2 he6 (oneB hg.bnd.A1 0) (by norm_num) (by norm_num)
    have hB := hg.B
    unfold HRaw.jd HRaw.G; split_ifs
    · have := addB (c := 21) hg.bnd.A2 (addB (c := 20) hg.bnd.A2 e1 e4 (by norm_num) (by norm_num)) e5
        (by norm_num) (by norm_num)
      omega
    · have := addB (c := 21) hg.bnd.A2 (addB (c := 20) hg.bnd.A2 e1 e3 (by norm_num) (by norm_num)) e5
        (by norm_num) (by norm_num)
      omega
  have r5 := Run.write (B := B) (σ := τ4) (ev_var (x := "d") (v := x.jd t) (by simp [hτ4, hτ3, Env.setVar]) hd)
  set τ5 := { τ4 with out := τ4.out ++ [x.jd t] } with hτ5
  have ht5 : τ5.vars "t" = t := by
    simp [hτ5, hτ4, hτ3, hτ2, Env.setVar]; rw [hv1 "t" (by decide), ht]
  have r6 := incrT_run (B := B) τ5 t ht5 (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by simp),
    by simp [Env.setVar], ?_, ?_, ?_⟩
  · simp only [Env.setVar, hτ5, hτ4, hτ3, hτ2]
    rw [ho1]; simp [HRaw.dueW]
  · simp only [Env.setVar, hτ5, hτ4, hτ3, hτ2]; rw [ha1]
  · intro y hy
    simp only [tempVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Env.setVar, hτ5, hτ4, hτ3, hτ2, hy.1, hy.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.2.2,
      if_false]
    exact hv1 y (by simp; tauto)

end Lax434175Proofs.JitEmit
