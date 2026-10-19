import Mathlib.Tactic
import Lax808846Proofs.Spec

/-!
Two pieces of the cost library for programs that read a word.

* A counted loop `x := 0; while x < m do c` whose invariant is indexed by the number of
  rounds done: `P k` says what the state is after `k` rounds. The cost is the one of
  `Spec.forRangeZero`, `(K_b + 4) N + 6`.
* A guarded read `v := a[e]` that gives `0` past the end of the word, as `List.getD`
  does, so a program can read any position a malformed word names.
-/

namespace Lax434175Proofs.Cost
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- `x := 0; while x < m do c` -/
abbrev forLoop (x m : String) (c : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c)

/-- **A counted loop with an invariant indexed by the number of rounds.** -/
theorem run_forLoop {B : ℕ} (x m : String) (c : Com) (N Kb : ℕ) (hNB : N < B)
    (P : ℕ → Env → Prop) (hx : ∀ k τ, P k τ → τ.vars x = k) (hm : ∀ k τ, P k τ → τ.vars m = N)
    (hbody : ∀ k < N, ∀ τ, P k τ → ∃ τ', Run B c τ τ' Kb ∧ P (k + 1) τ')
    {σ : Env} (h0 : P 0 (σ.setVar x 0)) :
    ∃ σ', Run B (forLoop x m c) σ σ' ((Kb + 4) * N + 6) ∧ P N σ' := by
  have hspec := Spec.forRangeZero (B := B) (c := c) x m (fun τ => ∃ k ≤ N, P k τ) N Kb hNB
    (fun τ ⟨k, hk, hP⟩ => (hx k τ hP) ▸ hk) (fun τ ⟨k, _, hP⟩ => hm k τ hP)
    (fun τ ⟨⟨k, hk, hP⟩, hlt⟩ => by
      have hxk := hx k τ hP
      obtain ⟨τ', hr, hP'⟩ := hbody k (by omega) τ hP
      exact ⟨τ', hr, ⟨k + 1, by omega, hP'⟩, by rw [hx _ _ hP', hxk]⟩)
  obtain ⟨σ', hr, ⟨k, hk, hP⟩, hN⟩ := hspec σ ⟨0, Nat.zero_le _, h0⟩
  have : k = N := (hx k σ' hP).symm.trans hN
  subst this
  exact ⟨σ', hr, hP⟩

/-- `v := a[e]` when `e < L`, else `v := 0`. -/
def rdG (a L v : String) (e : Expr) : Com :=
  .ite (.lt e (.var L)) (.assign v (.get a e)) (.assign v (.lit 0))

/-- **The guarded read is `List.getD`.** -/
theorem run_rdG {B : ℕ} {a L v : String} {e : Expr} {σ : Env} {u : List ℕ} {N idx : ℕ}
    (ha : σ.arrs a = arrOf N fun j => u.getD j 0) (hL : σ.vars L = u.length) (hN : u.length ≤ N)
    (he : e.evalB B σ = some idx) (huB : ∀ j, u.getD j 0 < B) (hLB : u.length < B) :
    Run B (rdG a L v e) σ (σ.setVar v (u.getD idx 0)) (2 * e.size + 5) := by
  have hc : (Cond.lt e (.var L)).evalB B σ = some (decide (idx < u.length)) :=
    evalB_condLt he (by rw [← hL]; exact evalB_var (by rw [hL]; exact hLB))
  by_cases hlt : idx < u.length
  · have hg : (Expr.get a e).evalB B σ = some (u.getD idx 0) :=
      evalB_get he (by rw [ha]; exact getElem?_arrOf _ (by omega)) (huB idx)
    exact (Run.ite_true (by rw [hc]; simp [hlt]) (Run.assign hg)).mono (by simp [size_condLt]; omega)
  · have h0 : u.getD idx 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h0]
    exact (Run.ite_false (by rw [hc]; simp [hlt]) (Run.assign (evalB_lit (by omega)))).mono
      (by simp [size_condLt]; omega)

end Lax434175Proofs.Cost
