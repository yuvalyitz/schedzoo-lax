import Mathlib.Tactic
import Lax434175Proofs.JitEmitProg

/-!
The walk of the emitter's program: after `i` rounds its variables hold the state of
`JitRaw.wstep` folded over the first `i` numbers after the header, and its two arrays the
membership pairs read.
-/

namespace Lax434175Proofs.JitEmit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.JitRaw Lax434175Proofs.JitWords
open Lax434175Proofs.Cost (forLoop run_forLoop rdG run_rdG)
open Lax434175Proofs.ThresholdProgram (ev_lit ev_var ev_add ev_mul ev_sub)

/-! ### The walk, round by round -/

/-- The state of the walk after `i` numbers. -/
def sAt (z : List ℕ) (i : ℕ) : WS := ((z.drop 3).take i).foldl wstep ⟨0, 0, []⟩

theorem sAt_succ (z : List ℕ) {i : ℕ} (hi : i + 3 < z.length) :
    sAt z (i + 1) = wstep (sAt z i) (z.getD (i + 3) 0) := by
  unfold sAt
  rw [List.take_add_one, List.foldl_append]
  have h : (z.drop 3)[i]? = some (z.getD (i + 3) 0) := by
    rw [List.getElem?_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp [Nat.add_comm, List.getElem?_eq_getElem (show i + 3 < z.length by omega)]
  rw [h]; rfl

theorem sAt_full (z : List ℕ) : sAt z (z.length - 3) = walk z := by
  unfold sAt walk
  rw [List.take_of_length_le (by simp)]

/-- The bounds of the walk. -/
structure SBd (z : List ℕ) (i : ℕ) (s : WS) : Prop where
  jj : s.jj ≤ i
  len : s.L.length ≤ i
  rem : s.rem ≤ Lax434175.Results.maxEntry z
  fst : ∀ p ∈ s.L, p.1 < i
  snd : ∀ p ∈ s.L, p.2 ≤ Lax434175.Results.maxEntry z

theorem getD_le (z : List ℕ) (q : ℕ) : z.getD q 0 ≤ Lax434175.Results.maxEntry z :=
  Lax434175Proofs.IsemPrograms.getD_le_max z q

theorem sBd (z : List ℕ) : ∀ i, i + 3 ≤ z.length → SBd z i (sAt z i)
  | 0, _ => ⟨by simp [sAt], by simp [sAt], by simp [sAt], by simp [sAt], by simp [sAt]⟩
  | i + 1, hi => by
    have ih := sBd z i (by omega)
    rw [sAt_succ z (by omega)]
    have hv := getD_le z (i + 3)
    unfold wstep
    split_ifs with h
    · exact ⟨by have := ih.jj; simp; omega, by have := ih.len; simp; omega, hv,
        fun p hp => by have := ih.fst p hp; omega, ih.snd⟩
    · refine ⟨by have := ih.jj; simp; omega, by have := ih.len; simp; omega,
        by have := ih.rem; simp; omega, fun p hp => ?_, fun p hp => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · have := ih.fst p hp; omega
        · have := ih.jj; simp; omega
      · simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact ih.snd p hp
        · exact hv

/-! ### The program's walk -/

/-- The array of the first components of the pairs. -/
def fstArr (n : ℕ) (L : List (ℕ × ℕ)) : List ℕ := arrOf n fun q => (L.getD q (0, 0)).1

/-- The array of the second components of the pairs. -/
def sndArr (n : ℕ) (L : List (ℕ × ℕ)) : List ℕ := arrOf n fun q => (L.getD q (0, 0)).2

theorem fstArr_snoc (n : ℕ) (L : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    (fstArr n L).set L.length p.1 = fstArr n (L ++ [p]) := by
  unfold fstArr
  rw [set_arrOf]
  refine arrOf_congr fun q _ => ?_
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_ge q L.length with h' | h'
    · rw [List.getD_append _ _ _ _ h']
    · rw [List.getD_eq_default _ _ h', List.getD_eq_default _ _ (by simp; omega)]

theorem sndArr_snoc (n : ℕ) (L : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    (sndArr n L).set L.length p.2 = sndArr n (L ++ [p]) := by
  unfold sndArr
  rw [set_arrOf]
  refine arrOf_congr fun q _ => ?_
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_ge q L.length with h' | h'
    · rw [List.getD_append _ _ _ _ h']
    · rw [List.getD_eq_default _ _ h', List.getD_eq_default _ _ (by simp; omega)]

/-- The variables the walk writes. -/
def walkVars : List String := ["i", "jj", "rem", "e"]

/-- The state of the program after `i` rounds of the walk. -/
structure WInv (z : List ℕ) (σ0 : Env) (r : ℕ) (τ : Env) : Prop where
  vi : τ.vars "i" = r
  vjj : τ.vars "jj" = (sAt z r).jj
  vrem : τ.vars "rem" = (sAt z r).rem
  ve : τ.vars "e" = (sAt z r).L.length
  va : τ.arrs "a" = arrOf z.length fun q => z.getD q 0
  vMJ : τ.arrs "MJ" = fstArr z.length (sAt z r).L
  vMI : τ.arrs "MI" = sndArr z.length (sAt z r).L
  vars : ∀ y ∉ walkVars, τ.vars y = σ0.vars y
  arrs : ∀ b, b ≠ "MJ" → b ≠ "MI" → τ.arrs b = σ0.arrs b
  out : τ.out = σ0.out

theorem walkBody_run {B : ℕ} (z : List ℕ) (hB : z.length + Lax434175.Results.maxEntry z + 8 < B)
    (σ0 : Env) (i : ℕ) (hi : i < z.length - 3) (τ : Env)
    (hw : WInv z σ0 i τ) :
    ∃ τ', Run B walkBody τ τ' 60 ∧ WInv z σ0 (i + 1) τ' := by
  have hbd := sBd z i (by omega)
  have hv := getD_le z (i + 3)
  have hs := sAt_succ z (i := i) (by omega)
  have hget : (Expr.get "a" (add (V "i") (.lit 3))).evalB B τ = some (z.getD (i + 3) 0) :=
    evalB_get (ev_add (ev_var hw.vi (by omega)) (ev_lit (by omega)) (by omega))
      (by rw [hw.va, getElem?_arrOf _ (by omega)]) (by omega)
  have hc : (Cond.eq (V "rem") (.lit 0)).evalB B τ = some ((sAt z i).rem == 0) := by
    rw [evalB_condEq (ev_var hw.vrem (by have := hbd.rem; omega)) (ev_lit (by omega))]
  have hfi : ∀ τ' : Env, τ'.vars "i" = i → τ'.vars "i" + 1 < B → Run B (incr "i") τ'
      (τ'.setVar "i" (i + 1)) 4 := fun τ' h h' =>
    (Run.assign (B := B) (σ := τ') (ev_add (ev_var h (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
  by_cases h0 : (sAt z i).rem = 0
  · have r1 := Run.assign (x := "jj") (B := B) (σ := τ) (ev_add (ev_var hw.vjj (by have := hbd.jj; omega))
      (ev_lit (n := 1) (by omega)) (by have := hbd.jj; omega))
    set τ1 := τ.setVar "jj" ((sAt z i).jj + 1) with hτ1
    have hget1 : (Expr.get "a" (add (V "i") (.lit 3))).evalB B τ1 = some (z.getD (i + 3) 0) :=
      evalB_get (ev_add (ev_var (x := "i") (v := i) (by simp [hτ1, Env.setVar, hw.vi]) (by omega))
        (ev_lit (n := 3) (by omega)) (by omega))
        (by simp only [hτ1, Env.setVar]; rw [hw.va, getElem?_arrOf _ (by omega)])
        (by omega)
    have r2 := Run.assign (x := "rem") (B := B) (σ := τ1) hget1
    set τ2 := τ1.setVar "rem" (z.getD (i + 3) 0) with hτ2
    have r3 := hfi τ2 (by simp [hτ2, hτ1, Env.setVar, hw.vi]) (by simp [hτ2, hτ1, Env.setVar, hw.vi]; omega)
    refine ⟨_, ((Run.ite_true (by rw [hc, h0]; rfl) (r1.seq r2)).seq r3).mono (by simp), ?_⟩
    have hs' : sAt z (i + 1) = ⟨(sAt z i).jj + 1, z.getD (i + 3) 0, (sAt z i).L⟩ := by
      rw [hs, wstep, if_pos h0]
    refine ⟨by simp [Env.setVar], by simp [hτ2, hτ1, Env.setVar, hs'],
      by simp [hτ2, hτ1, Env.setVar, hs'], by simp [hτ2, hτ1, Env.setVar, hs', hw.ve],
      by simp [hτ2, hτ1, Env.setVar, hw.va], by simp [hτ2, hτ1, Env.setVar, hs', hw.vMJ],
      by simp [hτ2, hτ1, Env.setVar, hs', hw.vMI], fun y hy => ?_, fun b h1 h2 => ?_, ?_⟩
    · simp only [walkVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hτ2, hτ1, Env.setVar, hy.1, hy.2.1, hy.2.2.1, hw.vars y (by simp [walkVars]; tauto)]
    · simp [hτ2, hτ1, Env.setVar, hw.arrs b h1 h2]
    · simp [hτ2, hτ1, Env.setVar, hw.out]
  · have he : (sAt z i).L.length < z.length := by have := hbd.len; omega
    have r1 := Run.store (a := "MJ") (B := B) (σ := τ) (ev_var hw.ve (by omega))
      (ev_sub (ev_var hw.vjj (by have := hbd.jj; omega)) (ev_lit (n := 1) (by omega)))
      (by rw [hw.vMJ]; unfold fstArr; simp; exact he)
    set τ1 := τ.setArr "MJ" (sAt z i).L.length ((sAt z i).jj - 1) with hτ1
    have hget1 : (Expr.get "a" (add (V "i") (.lit 3))).evalB B τ1 = some (z.getD (i + 3) 0) :=
      evalB_get (ev_add (ev_var (x := "i") (v := i) (by simp [hτ1, Env.setArr, hw.vi]) (by omega))
        (ev_lit (n := 3) (by omega)) (by omega)) (by
          simp only [hτ1, Env.setArr, show ("a" : String) ≠ "MJ" by decide, if_false]
          rw [hw.va, getElem?_arrOf _ (by omega)]) (by omega)
    have r2 := Run.store (a := "MI") (B := B) (σ := τ1)
      (ev_var (x := "e") (v := (sAt z i).L.length) (by simp [hτ1, Env.setArr, hw.ve]) (by omega)) hget1
      (by
        simp only [hτ1, Env.setArr, show ("MI" : String) ≠ "MJ" by decide, if_false]
        rw [hw.vMI]; unfold sndArr; simp; exact he)
    set τ2 := τ1.setArr "MI" (sAt z i).L.length (z.getD (i + 3) 0) with hτ2
    have r3 := Run.assign (x := "e") (B := B) (σ := τ2)
      (ev_add (ev_var (x := "e") (v := (sAt z i).L.length) (by simp [hτ2, hτ1, Env.setArr, hw.ve]) (by omega))
        (ev_lit (n := 1) (by omega))
        (by omega))
    set τ3 := τ2.setVar "e" ((sAt z i).L.length + 1) with hτ3
    have r4 := Run.assign (x := "rem") (B := B) (σ := τ3)
      (ev_sub (ev_var (x := "rem") (v := (sAt z i).rem) (by simp [hτ3, hτ2, hτ1, Env.setArr, Env.setVar, hw.vrem])
        (by have := hbd.rem; omega)) (ev_lit (n := 1) (by omega)))
    set τ4 := τ3.setVar "rem" ((sAt z i).rem - 1) with hτ4
    have r5 := hfi τ4 (by simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hw.vi])
      (by simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hw.vi]; omega)
    refine ⟨_, ((Run.ite_false (by rw [hc]; simp [h0]) (r1.seq (r2.seq (r3.seq r4)))).seq r5).mono
      (by simp), ?_⟩
    have hs' : sAt z (i + 1) = ⟨(sAt z i).jj, (sAt z i).rem - 1,
        (sAt z i).L ++ [((sAt z i).jj - 1, z.getD (i + 3) 0)]⟩ := by
      rw [hs, wstep, if_neg h0]
    refine ⟨by simp [Env.setVar], by simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hs', hw.vjj],
      by simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hs'],
      by simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hs'],
      by simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hw.va], ?_, ?_,
      fun y hy => ?_, fun b h1 h2 => ?_, ?_⟩
    · simp only [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hs']
      simp only [show ("MJ" : String) ≠ "MI" by decide, if_false, if_true]
      rw [hw.vMJ, ← fstArr_snoc]
    · simp only [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hs']
      simp only [show ("MI" : String) ≠ "MJ" by decide, if_false, if_true]
      rw [hw.vMI, ← sndArr_snoc]
    · simp only [walkVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hy.1, hy.2.2.1, hy.2.2.2,
        hw.vars y (by simp [walkVars]; tauto)]
    · simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, h1, h2, hw.arrs b h1 h2]
    · simp [hτ4, hτ3, hτ2, hτ1, Env.setVar, Env.setArr, hw.out]

theorem dtrue {p : Prop} [Decidable p] (h : p) : some (decide p) = some true := by simp [h]
theorem dfalse {p : Prop} [Decidable p] (h : ¬ p) : some (decide p) = some false := by simp [h]
theorem btrue {a b : ℕ} (h : a = b) : some (a == b) = some true := by simp [h]
theorem bfalse {a b : ℕ} (h : ¬ a = b) : some (a == b) = some false := by simp [h]

/-- What the check needs before it starts. -/
structure Pre (z : List ℕ) (σ : Env) : Prop where
  L : σ.vars "L" = z.length
  n : σ.vars "n" = z.getD 0 0
  m : σ.vars "m" = z.getD 1 0
  k : σ.vars "k" = z.getD 2 0
  a : σ.arrs "a" = arrOf z.length fun q => z.getD q 0
  MJ : σ.arrs "MJ" = fstArr z.length []
  MI : σ.arrs "MI" = sndArr z.length []

theorem walkCom_run {B : ℕ} (z : List ℕ) (hB : z.length + Lax434175.Results.maxEntry z + 8 < B)
    (σ : Env) (hp : Pre z σ) :
    ∃ τ, Run B walkCom σ τ (64 * z.length + 30) ∧ τ.vars "jj" = (walk z).jj ∧
      τ.vars "rem" = (walk z).rem ∧ τ.vars "e" = (walk z).L.length ∧
      τ.arrs "MJ" = fstArr z.length (walk z).L ∧ τ.arrs "MI" = sndArr z.length (walk z).L ∧
      τ.arrs "a" = σ.arrs "a" ∧ τ.out = σ.out ∧
      (∀ y ∉ ["i", "jj", "rem", "e", "L3"], τ.vars y = σ.vars y) := by
  have r1 := Run.assign (x := "jj") (B := B) (σ := σ) (ev_lit (n := 0) (by omega))
  set σ1 := σ.setVar "jj" 0 with hσ1
  have r2 := Run.assign (x := "rem") (B := B) (σ := σ1) (ev_lit (n := 0) (by omega))
  set σ2 := σ1.setVar "rem" 0 with hσ2
  have r3 := Run.assign (x := "e") (B := B) (σ := σ2) (ev_lit (n := 0) (by omega))
  set σ3 := σ2.setVar "e" 0 with hσ3
  have r4 := Run.assign (x := "L3") (B := B) (σ := σ3)
    (ev_sub (ev_var (x := "L") (v := z.length) (by simp [hσ3, hσ2, hσ1, Env.setVar, hp.L])
      (by omega)) (ev_lit (n := 3) (by omega)))
  set σ0 := σ3.setVar "L3" (z.length - 3) with hσ0
  obtain ⟨τ, r5, hw⟩ := run_forLoop (B := B) "i" "L3" walkBody (z.length - 3) 60 (by omega)
    (fun r τ => WInv z σ0 r τ) (fun _ _ h => h.vi)
    (fun _ τ h => by rw [h.vars "L3" (by simp [walkVars])]; simp [hσ0, Env.setVar])
    (fun r hr τ h => walkBody_run z hB σ0 r hr τ h)
    (σ := σ0) ⟨by simp [Env.setVar], by simp [hσ0, hσ3, hσ2, hσ1, Env.setVar, sAt],
      by simp [hσ0, hσ3, hσ2, hσ1, Env.setVar, sAt], by simp [hσ0, hσ3, hσ2, hσ1, Env.setVar, sAt],
      by simp [hσ0, hσ3, hσ2, hσ1, Env.setVar, hp.a],
      by simp [hσ0, hσ3, hσ2, hσ1, Env.setVar, hp.MJ, sAt],
      by simp [hσ0, hσ3, hσ2, hσ1, Env.setVar, hp.MI, sAt],
      fun y hy => by
        simp only [walkVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [Env.setVar, hy.1], fun b _ _ => rfl, rfl⟩
  have e1 := hw.vjj
  have e2 := hw.vrem
  have e3 := hw.ve
  have e4 := hw.vMJ
  have e5 := hw.vMI
  rw [sAt_full] at e1 e2 e3 e4 e5
  refine ⟨τ, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by simp; omega), e1, e2, e3,
    e4, e5, by rw [hw.arrs "a" (by decide) (by decide)]; simp [hσ0, hσ3, hσ2, hσ1, Env.setVar],
    by rw [hw.out]; simp [hσ0, hσ3, hσ2, hσ1, Env.setVar], fun y hy => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  rw [hw.vars y (by simp [walkVars]; tauto)]
  simp [hσ0, hσ3, hσ2, hσ1, Env.setVar, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2]

/-- What the check leaves: `ok`, and for numbers of an instance the pairs in the arrays. -/
structure Post (z : List ℕ) (σ τ : Env) : Prop where
  ok : τ.vars "ok" = if okH z then 1 else 0
  e : okH z → τ.vars "e" = (walk z).L.length
  MJ : okH z → τ.arrs "MJ" = fstArr z.length (walk z).L
  MI : okH z → τ.arrs "MI" = sndArr z.length (walk z).L
  out : τ.out = σ.out
  vars : ∀ y ∉ ["i", "jj", "rem", "e", "L3", "ok"], τ.vars y = σ.vars y

theorem chkCom_run {B : ℕ} (z : List ℕ) (hB : z.length + Lax434175.Results.maxEntry z + 8 < B)
    (σ : Env) (hp : Pre z σ) :
    ∃ τ, Run B chkCom σ τ (64 * z.length + 100) ∧ Post z σ τ := by
  have hle := fun q => getD_le z q
  have r0 := Run.assign (x := "ok") (B := B) (σ := σ) (ev_lit (n := 0) (by omega))
  set σ0 := σ.setVar "ok" 0 with hσ0
  have hp0 : Pre z σ0 := ⟨by simp [hσ0, Env.setVar, hp.L], by simp [hσ0, Env.setVar, hp.n],
    by simp [hσ0, Env.setVar, hp.m], by simp [hσ0, Env.setVar, hp.k], by simp [hσ0, Env.setVar, hp.a],
    by simp [hσ0, Env.setVar, hp.MJ], by simp [hσ0, Env.setVar, hp.MI]⟩
  have hL : σ0.vars "L" = z.length := hp0.L
  have hn : σ0.vars "n" = z.getD 0 0 := hp0.n
  have hk : σ0.vars "k" = z.getD 2 0 := hp0.k
  have hn' := hle 0
  have hk' := hle 2
  have c1 : (Cond.lt (.lit 2) (V "L")).evalB B σ0 = some (decide (2 < z.length)) :=
    evalB_condLt (ev_lit (by omega)) (ev_var hL (by omega))
  have c2 : (Cond.lt (V "n") (add (V "L") (.lit 5))).evalB B σ0 =
      some (decide (z.getD 0 0 < z.length + 5)) :=
    evalB_condLt (ev_var hn (by omega)) (ev_add (ev_var hL (by omega)) (ev_lit (by omega)) (by omega))
  have c3 : (Cond.lt (V "k") (add (V "n") (.lit 1))).evalB B σ0 =
      some (decide (z.getD 2 0 < z.getD 0 0 + 1)) :=
    evalB_condLt (ev_var hk (by omega)) (ev_add (ev_var hn (by omega)) (ev_lit (by omega)) (by omega))
  have hnot : ∀ τ : Env, τ = σ0 → ¬ okH z → Post z σ τ := fun τ hτ hno => by
    subst hτ
    exact ⟨by simp [hσ0, Env.setVar, hno], fun h => absurd h hno, fun h => absurd h hno,
      fun h => absurd h hno, by simp [hσ0, Env.setVar],
      fun y hy => by simp at hy; simp [hσ0, Env.setVar, hy]⟩
  by_cases h1 : 2 < z.length
  · by_cases h2 : z.getD 0 0 < z.length + 5
    · by_cases h3 : z.getD 2 0 < z.getD 0 0 + 1
      · obtain ⟨τ, rw, hjj, hrem, he, hMJ, hMI, ha, ho, hv⟩ := walkCom_run z hB σ0 hp0
        have hjB : (walk z).jj ≤ z.length := by
          have := (sBd z (z.length - 3) (by omega)).jj; rw [sAt_full] at this; omega
        have hrB : (walk z).rem ≤ Lax434175.Results.maxEntry z := by
          have := (sBd z (z.length - 3) (by omega)).rem; rw [sAt_full] at this; omega
        have hm : τ.vars "m" = z.getD 1 0 := by rw [hv "m" (by decide)]; exact hp0.m
        have hm' := hle 1
        have c4 : (Cond.eq (V "rem") (.lit 0)).evalB B τ = some ((walk z).rem == 0) :=
          evalB_condEq (ev_var hrem (by omega)) (ev_lit (by omega))
        have c5 : (Cond.eq (V "jj") (V "m")).evalB B τ = some ((walk z).jj == z.getD 1 0) :=
          evalB_condEq (ev_var hjj (by omega)) (ev_var hm (by omega))
        have hpost : ∀ τ', τ'.vars "ok" = (if okH z then 1 else 0) →
            (τ' = τ ∨ τ' = τ.setVar "ok" 1) → Post z σ τ' := fun τ' hok hτ' => by
          have hτa : τ'.arrs = τ.arrs := by rcases hτ' with rfl | rfl <;> rfl
          have hτo : τ'.out = τ.out := by rcases hτ' with rfl | rfl <;> rfl
          have hτe : τ'.vars "e" = τ.vars "e" := by rcases hτ' with rfl | rfl <;> simp [Env.setVar]
          refine ⟨hok, fun _ => by rw [hτe, he], fun _ => by rw [hτa, hMJ],
            fun _ => by rw [hτa, hMI],
            by rw [hτo, ho]; simp [hσ0, Env.setVar], fun y hy => ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          have : τ'.vars y = τ.vars y := by
            rcases hτ' with rfl | rfl
            · rfl
            · simp [Env.setVar, hy.2.2.2.2.2]
          rw [this, hv y (by simp; tauto)]
          simp [hσ0, Env.setVar, hy.2.2.2.2.2]
        by_cases h4 : (walk z).rem = 0
        · by_cases h5 : (walk z).jj = z.getD 1 0
          · have hok : okH z := ⟨by omega, by omega, by omega, h4, h5⟩
            refine ⟨_, (r0.seq (Run.ite_true (by rw [c1]; exact dtrue h1) (Run.ite_true (by rw [c2]; exact dtrue h2)
              (Run.ite_true (by rw [c3]; exact dtrue h3) (rw.seq (Run.ite_true (by rw [c4]; exact btrue h4)
                (Run.ite_true (by rw [c5]; exact btrue h5)
                  (Run.assign (x := "ok") (B := B) (σ := τ) (ev_lit (n := 1) (by omega)))))))))).mono
              (by simp; omega), hpost _ (by simp [Env.setVar, hok]) (Or.inr rfl)⟩
          · have hno : ¬ okH z := fun h => h5 h.2.2.2.2
            refine ⟨_, (r0.seq (Run.ite_true (by rw [c1]; exact dtrue h1) (Run.ite_true (by rw [c2]; exact dtrue h2)
              (Run.ite_true (by rw [c3]; exact dtrue h3) (rw.seq (Run.ite_true (by rw [c4]; exact btrue h4)
                (Run.ite_false (by rw [c5]; exact bfalse h5) Run.skip))))))).mono
              (by simp; omega), hpost _ ?_ (Or.inl rfl)⟩
            rw [hv "ok" (by decide)]; simp [hσ0, Env.setVar, hno]
        · have hno : ¬ okH z := fun h => h4 h.2.2.2.1
          refine ⟨_, (r0.seq (Run.ite_true (by rw [c1]; exact dtrue h1) (Run.ite_true (by rw [c2]; exact dtrue h2)
            (Run.ite_true (by rw [c3]; exact dtrue h3) (rw.seq (Run.ite_false (by rw [c4]; exact bfalse h4)
              Run.skip)))))).mono (by simp; omega), hpost _ ?_ (Or.inl rfl)⟩
          rw [hv "ok" (by decide)]; simp [hσ0, Env.setVar, hno]
      · have hno : ¬ okH z := fun h => h3 (by have := h.2.2.1; omega)
        exact ⟨_, (r0.seq (Run.ite_true (by rw [c1]; exact dtrue h1) (Run.ite_true (by rw [c2]; exact dtrue h2)
          (Run.ite_false (by rw [c3]; exact dfalse h3) Run.skip)))).mono (by simp),
          hnot _ rfl hno⟩
    · have hno : ¬ okH z := fun h => h2 (by have := h.2.1; omega)
      exact ⟨_, (r0.seq (Run.ite_true (by rw [c1]; exact dtrue h1)
        (Run.ite_false (by rw [c2]; exact dfalse h2) Run.skip))).mono (by simp), hnot _ rfl hno⟩
  · have hno : ¬ okH z := fun h => h1 (by have := h.1; omega)
    exact ⟨_, (r0.seq (Run.ite_false (by rw [c1]; exact dfalse h1) Run.skip)).mono (by simp),
      hnot _ rfl hno⟩

end Lax434175Proofs.JitEmit
