import Mathlib.Tactic
import Lax808846Proofs.Spec

/-!
Composing IMP+ algorithms: the output of one becomes the input of the next.

`redirW buf k c` is `c` with every `write e` turned into `buf[k] := e; k := k + 1`, so
that what `c` writes ends up in the array `buf` from position `1` on. `redirR buf r c` is
`c` with every `read x` turned into `x := buf[r]; r := r + 1`, so that `c` reads the array
instead of the input. Both are simulations at a fixed price per construct: a redirected
run costs at most `4` times the original (writes), resp. `8` times (reads). The names
`buf`, `k`, `r` must not occur in `c`.
-/

namespace Lax434175Proofs.Cost
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

-- The names an expression, a condition, a command mention

def Expr.idents : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get a i => a :: Expr.idents i
  | .bin _ e f => Expr.idents e ++ Expr.idents f

def Cond.idents : Cond → List String
  | .eq e f => Expr.idents e ++ Expr.idents f
  | .lt e f => Expr.idents e ++ Expr.idents f

def Com.idents : Com → List String
  | .skip => []
  | .assign x e => x :: Expr.idents e
  | .store a i e => a :: (Expr.idents i ++ Expr.idents e)
  | .seq c d => Com.idents c ++ Com.idents d
  | .ite b c d => Cond.idents b ++ Com.idents c ++ Com.idents d
  | .while b c => Cond.idents b ++ Com.idents c
  | .read x => [x]
  | .write e => Expr.idents e

/-- Two environments agree on the names of a list. -/
def Agree (l : List String) (σ τ : Env) : Prop :=
  ∀ y ∈ l, τ.vars y = σ.vars y ∧ τ.arrs y = σ.arrs y

theorem Agree.mono {l l' : List String} {σ τ : Env} (h : Agree l σ τ) (hl : ∀ y ∈ l', y ∈ l) :
    Agree l' σ τ := fun y hy => h y (hl y hy)

theorem evalB_agree {B : ℕ} {σ τ : Env} : ∀ (e : Expr), Agree (Expr.idents e) σ τ →
    e.evalB B τ = e.evalB B σ
  | .lit _, _ => rfl
  | .var x, h => by simp only [Expr.evalB]; rw [(h x (by simp [Expr.idents])).1]
  | .get a i, h => by
      simp only [Expr.evalB]
      rw [evalB_agree i (h.mono (by simp [Expr.idents]; tauto)), (h a (by simp [Expr.idents])).2]
  | .bin _ e f, h => by
      simp only [Expr.evalB]
      rw [evalB_agree e (h.mono (by simp [Expr.idents]; tauto)),
        evalB_agree f (h.mono (by simp [Expr.idents]; tauto))]

theorem condB_agree {B : ℕ} {σ τ : Env} : ∀ (b : Cond), Agree (Cond.idents b) σ τ →
    b.evalB B τ = b.evalB B σ
  | .eq e f, h => by
      simp only [Cond.evalB]
      rw [evalB_agree e (h.mono (by simp [Cond.idents]; tauto)),
        evalB_agree f (h.mono (by simp [Cond.idents]; tauto))]
  | .lt e f, h => by
      simp only [Cond.evalB]
      rw [evalB_agree e (h.mono (by simp [Cond.idents]; tauto)),
        evalB_agree f (h.mono (by simp [Cond.idents]; tauto))]

theorem Expr.size_pos : ∀ e : Expr, 1 ≤ e.size
  | .lit _ => le_rfl
  | .var _ => le_rfl
  | .get _ i => by simp [size_get]
  | .bin _ e f => by simp [size_bin]

theorem out_prefix {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    ∃ w, σ'.out = σ.out ++ w := by
  induction h with
  | skip => exact ⟨[], by simp⟩
  | assign => exact ⟨[], by simp⟩
  | store => exact ⟨[], by simp⟩
  | seq _ _ ih1 ih2 => obtain ⟨w1, h1⟩ := ih1; obtain ⟨w2, h2⟩ := ih2; exact ⟨w1 ++ w2, by simp [h2, h1]⟩
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih1 ih2 =>
      obtain ⟨w1, h1⟩ := ih1; obtain ⟨w2, h2⟩ := ih2; exact ⟨w1 ++ w2, by simp [h2, h1]⟩
  | while_false => exact ⟨[], by simp⟩
  | read => exact ⟨[], by simp⟩
  | write => exact ⟨_, rfl⟩

-- Redirecting the writes

/-- Every `write e` becomes `buf[k] := e; k := k + 1`. -/
def redirW (buf k : String) : Com → Com
  | .write e => .seq (.store buf (.var k) e) (.assign k (.add (.var k) (.lit 1)))
  | .seq c d => .seq (redirW buf k c) (redirW buf k d)
  | .ite b c d => .ite b (redirW buf k c) (redirW buf k d)
  | .while b c => .while b (redirW buf k c)
  | c => c

/-- The buffer holding the output `o` from position `1` on. -/
def bufOf (N : ℕ) (o : List ℕ) : List ℕ := arrOf N fun i => if 1 ≤ i ∧ i ≤ o.length then o.getD (i - 1) 0 else 0

/-- The redirected state `τ` simulates `σ`: equal off `buf` and `k`, the output in the
buffer, `k` just past it, its own output unchanged. -/
structure WRel (S : List String) (buf k : String) (N : ℕ) (o : List ℕ) (σ τ : Env) : Prop where
  vars : ∀ y ∈ S, τ.vars y = σ.vars y
  arrs : ∀ a ∈ S, τ.arrs a = σ.arrs a
  inp : τ.inp = σ.inp
  out : τ.out = o
  kv : τ.vars k = σ.out.length + 1
  bufv : τ.arrs buf = bufOf N σ.out

theorem WRel.agree {S : List String} {buf k : String} {N : ℕ} {o : List ℕ} {σ τ : Env}
    (h : WRel S buf k N o σ τ) {l : List String} (hl : ∀ y ∈ l, y ∈ S) : Agree l σ τ := fun y hy =>
  ⟨h.vars y (hl y hy), h.arrs y (hl y hy)⟩

theorem bufOf_snoc {N : ℕ} (o : List ℕ) (v : ℕ) (hN : o.length + 1 < N) :
    (bufOf N o).set (o.length + 1) v = bufOf N (o ++ [v]) := by
  unfold bufOf
  rw [set_arrOf]
  refine arrOf_congr fun i _ => ?_
  by_cases hi : i = o.length + 1
  · subst hi
    rw [if_pos rfl, if_pos (by simp), List.getD_eq_getElem?_getD]
    simp
  · rw [if_neg hi]
    simp only [List.length_append, List.length_singleton]
    by_cases h1 : 1 ≤ i ∧ i ≤ o.length
    · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

/-- **Redirecting the writes is a simulation**, at most four times the cost. -/
theorem bigStep_redirW {B N : ℕ} {S : List String} {buf k : String} (hkS : k ∉ S) (hbS : buf ∉ S)
    (hkb : k ≠ buf) {o : List ℕ} :
    ∀ {c : Com} {σ σ' : Env} {K : ℕ}, BigStepB B c σ σ' K → (∀ y ∈ Com.idents c, y ∈ S) →
      σ'.out.length + 2 ≤ N → N < B → ∀ {τ : Env}, WRel S buf k N o σ τ →
      ∃ τ' K', BigStepB B (redirW buf k c) τ τ' K' ∧ K' ≤ 4 * K ∧ WRel S buf k N o σ' τ' := by
  intro c σ σ' K h
  induction h with
  | skip =>
    intro _ _ _ τ hr
    exact ⟨τ, 1, .skip, by omega, hr⟩
  | @assign σ x e v he =>
    intro hS _ _ τ hr
    have hev : e.evalB B τ = some v := by
      rw [evalB_agree e (hr.agree fun y hy => hS y (List.mem_cons_of_mem _ hy))]; exact he
    have hxS : x ∈ S := hS x List.mem_cons_self
    have hxk : k ≠ x := fun e => hkS (e ▸ hxS)
    refine ⟨_, _, .assign hev, by omega, ⟨fun y hy => ?_, hr.arrs, hr.inp, hr.out, ?_, hr.bufv⟩⟩
    · simp only [vars_setVar]; split_ifs <;> [rfl; exact hr.vars y hy]
    · simp [hxk, hr.kv]
  | @store σ a i e kk v hi he hkk =>
    intro hS _ _ τ hr
    have hi' : i.evalB B τ = some kk := by
      rw [evalB_agree i (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hi
    have he' : e.evalB B τ = some v := by
      rw [evalB_agree e (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact he
    have haS : a ∈ S := hS a (by simp [Com.idents])
    have hab : a ≠ buf := fun e => hbS (e ▸ haS)
    have hta : τ.arrs a = σ.arrs a := hr.arrs a haS
    refine ⟨_, _, .store hi' he' (by rw [hta]; exact hkk), by omega,
      ⟨hr.vars, fun b hb => ?_, hr.inp, hr.out, hr.kv, ?_⟩⟩
    · simp only [arrs_setArr]; split_ifs with hba
      · subst hba; rw [hta]
      · exact hr.arrs b hb
    · simp only [arrs_setArr, if_neg (Ne.symm hab)]; exact hr.bufv
  | seq h1 h2 ih1 ih2 =>
    intro hS hN hNB τ hr
    obtain ⟨w, hw⟩ := out_prefix h2
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih1 (fun y hy => hS y (by simp [Com.idents, hy]))
      (by rw [hw] at hN; simp at hN; omega) hNB hr
    obtain ⟨τ2, K2, r2, hK2, hr2⟩ := ih2 (fun y hy => hS y (by simp [Com.idents, hy])) hN hNB hr1
    exact ⟨τ2, K1 + K2, .seq r1 r2, by omega, hr2⟩
  | @ite_true b c d σ σ' kk hcb hc ih =>
    intro hS hN hNB τ hr
    have hcb' : b.evalB B τ = some true := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih (fun y hy => hS y (by simp [Com.idents, hy])) hN hNB hr
    exact ⟨τ1, _, .ite_true hcb' r1, by omega, hr1⟩
  | @ite_false b c d σ σ' kk hcb hd ih =>
    intro hS hN hNB τ hr
    have hcb' : b.evalB B τ = some false := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih (fun y hy => hS y (by simp [Com.idents, hy])) hN hNB hr
    exact ⟨τ1, _, .ite_false hcb' r1, by omega, hr1⟩
  | @while_true b c σ σ' σ'' kk kk' hcb hc hw ih1 ih2 =>
    intro hS hN hNB τ hr
    obtain ⟨w, hw'⟩ := out_prefix hw
    have hcb' : b.evalB B τ = some true := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih1 (fun y hy => hS y (by simp [Com.idents, hy]))
      (by rw [hw'] at hN; simp at hN; omega) hNB hr
    obtain ⟨τ2, K2, r2, hK2, hr2⟩ := ih2 hS hN hNB hr1
    exact ⟨τ2, _, .while_true hcb' r1 r2, by omega, hr2⟩
  | @while_false b c σ hcb =>
    intro hS _ _ τ hr
    have hcb' : b.evalB B τ = some false := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    exact ⟨τ, _, .while_false hcb', by omega, hr⟩
  | @read σ x v rest hin =>
    intro hS _ _ τ hr
    have hxS : x ∈ S := hS x (by simp [Com.idents])
    have hxk : k ≠ x := fun e => hkS (e ▸ hxS)
    refine ⟨_, _, .read (by rw [hr.inp]; exact hin), le_refl _ |>.trans (by omega),
      ⟨fun y hy => ?_, hr.arrs, rfl, hr.out, ?_, hr.bufv⟩⟩
    · simp only [vars_setVar]; split_ifs <;> [rfl; exact hr.vars y hy]
    · simp [hxk, hr.kv]
  | @write σ e v he =>
    intro hS hN hNB τ hr
    have he' : e.evalB B τ = some v := by
      rw [evalB_agree e (hr.agree fun y hy => hS y hy)]; exact he
    simp only [List.length_append, List.length_singleton] at hN
    have hst : BigStepB B (.store buf (.var k) e) τ (τ.setArr buf (σ.out.length + 1) v) (1 + 1 + e.size) :=
      .store (by rw [← hr.kv]; exact evalB_var (by rw [hr.kv]; omega)) he'
        (by rw [hr.bufv]; simp [bufOf]; omega)
    have hkv : (τ.setArr buf (σ.out.length + 1) v).vars k = σ.out.length + 1 := by simp [hr.kv]
    have hinc : BigStepB B (.assign k (.add (.var k) (.lit 1))) (τ.setArr buf (σ.out.length + 1) v)
        ((τ.setArr buf (σ.out.length + 1) v).setVar k (σ.out.length + 1 + 1)) (1 + 3) :=
      .assign (evalB_bin (by rw [← hkv]; exact evalB_var (by rw [hkv]; omega)) (evalB_lit (by omega))
        (by simp; omega))
    refine ⟨_, _, .seq hst hinc, by have := Expr.size_pos e; omega,
      ⟨fun y hy => ?_, fun a ha => ?_, by simp [hr.inp], by simp [hr.out], by simp, ?_⟩⟩
    · have : y ≠ k := fun e => hkS (e ▸ hy)
      simp [this, hr.vars y hy]
    · have : a ≠ buf := fun e => hbS (e ▸ ha)
      simp [this, hr.arrs a ha]
    · simp only [arrs_setVar, arrs_setArr, if_true]
      rw [hr.bufv]
      exact bufOf_snoc σ.out v (by omega)

-- Redirecting the reads

/-- Every `read x` becomes `x := buf[r]; r := r + 1`. -/
def redirR (buf r : String) : Com → Com
  | .read x => .seq (.assign x (.get buf (.var r))) (.assign r (.add (.var r) (.lit 1)))
  | .seq c d => .seq (redirR buf r c) (redirR buf r d)
  | .ite b c d => .ite b (redirR buf r c) (redirR buf r d)
  | .while b c => .while b (redirR buf r c)
  | c => c

/-- The redirected state `τ` simulates `σ`: equal off `buf` and `r`, the tape in the
buffer, `r` at the first number `σ` has not read, its own input unchanged. -/
structure RRel (S : List String) (buf r : String) (N : ℕ) (tape ι : List ℕ) (σ τ : Env) : Prop where
  vars : ∀ y ∈ S, τ.vars y = σ.vars y
  arrs : ∀ a ∈ S, τ.arrs a = σ.arrs a
  inp : τ.inp = ι
  out : τ.out = σ.out
  pos : σ.inp = tape.drop (τ.vars r)
  bufv : τ.arrs buf = arrOf N fun i => tape.getD i 0

theorem RRel.agree {S : List String} {buf r : String} {N : ℕ} {tape ι : List ℕ} {σ τ : Env}
    (h : RRel S buf r N tape ι σ τ) {l : List String} (hl : ∀ y ∈ l, y ∈ S) : Agree l σ τ := fun y hy =>
  ⟨h.vars y (hl y hy), h.arrs y (hl y hy)⟩

/-- **Redirecting the reads is a simulation**, at most eight times the cost. -/
theorem bigStep_redirR {B N : ℕ} {S : List String} {buf r : String} (hrS : r ∉ S) (hbS : buf ∉ S)
    (hrb : r ≠ buf) {tape ι : List ℕ} (hN : tape.length ≤ N) (hNB : N < B) (htB : ∀ i, tape.getD i 0 < B) :
    ∀ {c : Com} {σ σ' : Env} {K : ℕ}, BigStepB B c σ σ' K → (∀ y ∈ Com.idents c, y ∈ S) →
      ∀ {τ : Env}, RRel S buf r N tape ι σ τ →
      ∃ τ' K', BigStepB B (redirR buf r c) τ τ' K' ∧ K' ≤ 8 * K ∧ RRel S buf r N tape ι σ' τ' := by
  intro c σ σ' K h
  induction h with
  | skip =>
    intro _ τ hr
    exact ⟨τ, 1, .skip, by omega, hr⟩
  | @assign σ x e v he =>
    intro hS τ hr
    have hev : e.evalB B τ = some v := by
      rw [evalB_agree e (hr.agree fun y hy => hS y (List.mem_cons_of_mem _ hy))]; exact he
    have hxS : x ∈ S := hS x List.mem_cons_self
    have hxr : r ≠ x := fun e => hrS (e ▸ hxS)
    refine ⟨_, _, .assign hev, by omega, ⟨fun y hy => ?_, hr.arrs, hr.inp, hr.out, ?_, hr.bufv⟩⟩
    · simp only [vars_setVar]; split_ifs <;> [rfl; exact hr.vars y hy]
    · simp [hxr, hr.pos]
  | @store σ a i e kk v hi he hkk =>
    intro hS τ hr
    have hi' : i.evalB B τ = some kk := by
      rw [evalB_agree i (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hi
    have he' : e.evalB B τ = some v := by
      rw [evalB_agree e (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact he
    have haS : a ∈ S := hS a (by simp [Com.idents])
    have hab : a ≠ buf := fun e => hbS (e ▸ haS)
    have hta : τ.arrs a = σ.arrs a := hr.arrs a haS
    refine ⟨_, _, .store hi' he' (by rw [hta]; exact hkk), by omega,
      ⟨hr.vars, fun b hb => ?_, hr.inp, hr.out, hr.pos, ?_⟩⟩
    · simp only [arrs_setArr]; split_ifs with hba
      · subst hba; rw [hta]
      · exact hr.arrs b hb
    · simp only [arrs_setArr, if_neg (Ne.symm hab)]; exact hr.bufv
  | seq h1 h2 ih1 ih2 =>
    intro hS τ hr
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih1 (fun y hy => hS y (by simp [Com.idents, hy])) hr
    obtain ⟨τ2, K2, r2, hK2, hr2⟩ := ih2 (fun y hy => hS y (by simp [Com.idents, hy])) hr1
    exact ⟨τ2, K1 + K2, .seq r1 r2, by omega, hr2⟩
  | @ite_true b c d σ σ' kk hcb hc ih =>
    intro hS τ hr
    have hcb' : b.evalB B τ = some true := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih (fun y hy => hS y (by simp [Com.idents, hy])) hr
    exact ⟨τ1, _, .ite_true hcb' r1, by omega, hr1⟩
  | @ite_false b c d σ σ' kk hcb hd ih =>
    intro hS τ hr
    have hcb' : b.evalB B τ = some false := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih (fun y hy => hS y (by simp [Com.idents, hy])) hr
    exact ⟨τ1, _, .ite_false hcb' r1, by omega, hr1⟩
  | @while_true b c σ σ' σ'' kk kk' hcb hc hw ih1 ih2 =>
    intro hS τ hr
    have hcb' : b.evalB B τ = some true := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    obtain ⟨τ1, K1, r1, hK1, hr1⟩ := ih1 (fun y hy => hS y (by simp [Com.idents, hy])) hr
    obtain ⟨τ2, K2, r2, hK2, hr2⟩ := ih2 hS hr1
    exact ⟨τ2, _, .while_true hcb' r1 r2, by omega, hr2⟩
  | @while_false b c σ hcb =>
    intro hS τ hr
    have hcb' : b.evalB B τ = some false := by
      rw [condB_agree b (hr.agree fun y hy => hS y (by simp [Com.idents, hy]))]; exact hcb
    exact ⟨τ, _, .while_false hcb', by omega, hr⟩
  | @read σ x v rest hin =>
    intro hS τ hr
    have hxS : x ∈ S := hS x (by simp [Com.idents])
    have hxr : x ≠ r := fun e => hrS (e ▸ hxS)
    set p := τ.vars r with hp
    have hdrop : tape.drop p = v :: rest := hr.pos.symm.trans hin
    have hpl : p < tape.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hdrop
      exact absurd hdrop (by simp)
    have hcons := List.drop_eq_getElem_cons hpl
    rw [hdrop] at hcons
    simp only [List.cons.injEq] at hcons
    have hv : tape.getD p 0 = v := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpl]; simp [hcons.1]
    have hget : (Expr.get buf (.var r)).evalB B τ = some v := by
      rw [← hv]
      exact evalB_get (evalB_var (by omega)) (by rw [hr.bufv]; exact getElem?_arrOf _ (by omega)) (htB p)
    set τ1 := τ.setVar x v
    have hr1 : τ1.vars r = p := by simp [τ1, Ne.symm hxr, hp]
    have hinc : BigStepB B (.assign r (.add (.var r) (.lit 1))) τ1 (τ1.setVar r (p + 1)) (1 + 3) :=
      .assign (evalB_bin (by rw [← hr1]; exact evalB_var (by rw [hr1]; omega)) (evalB_lit (by omega))
        (by simp; omega))
    refine ⟨_, _, .seq (.assign hget) hinc, by simp, ⟨fun y hy => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_⟩⟩
    · have : y ≠ r := fun e => hrS (e ▸ hy)
      simp only [τ1, vars_setVar, if_neg this]
      split_ifs <;> [rfl; exact hr.vars y hy]
    · simp [τ1, hr.arrs a ha]
    · simp [τ1, hr.inp]
    · simp [τ1, hr.out]
    · simp only [vars_setVar, if_true]; exact hcons.2
    · simp [τ1, hr.bufv]
  | @write σ e v he =>
    intro hS τ hr
    have he' : e.evalB B τ = some v := by
      rw [evalB_agree e (hr.agree fun y hy => hS y hy)]; exact he
    exact ⟨_, _, .write he', by omega, ⟨hr.vars, hr.arrs, hr.inp, by simp [hr.out], hr.pos, hr.bufv⟩⟩

end Lax434175Proofs.Cost
