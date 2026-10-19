import Mathlib.Tactic
import Lax808846Proofs.Spec

/-!
Closed-form costs of nested counted loops.

`Spec.forRangeZero` of lax-808846 gives one scan `x := 0; while x < m do c` the
cost `(K_b + 4) N + 6`, for a body of cost `K_b`. Two nested scans

```
x := 0; while x < m do ((y := 0; while y < k do c); x := x + 1)
```

cost `((K_b + 4) M + 14) N + 6` — the inner scan, the increment of `x` (cost
`4`), and the outer loop's own overhead. The caller gives an outer invariant
`I`, an inner invariant `J`, what holds on entering the inner scan, and what the
finished inner scan gives back to the outer one.
-/

namespace Lax434175Proofs.Cost
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

variable {B : ℕ} {c : Com}

/-- The increment `x := x + 1`. -/
def incr (x : String) : Com := .assign x (.bin .add (.var x) (.lit 1))

/-- The command of two nested counted scans from zero. -/
def scan2 (x m y k : String) (c : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m))
    (.seq (.seq (.assign y (.lit 0)) (.while (.lt (.var y) (.var k)) c)) (incr x)))

/-- The increment, while the counter stays below the bound. -/
theorem spec_incr {P : Env → Prop} (x : String) (h : ∀ σ, P σ → σ.vars x + 1 < B) :
    Spec B P (incr x) (fun σ σ' => σ' = σ.setVar x (σ.vars x + 1)) 4 := by
  have := Spec.assign (B := B) (P := P) (x := x) (e := .bin .add (.var x) (.lit 1))
    (f := fun σ => σ.vars x + 1) fun σ hσ =>
      evalB_bin (evalB_var (by have := h σ hσ; omega)) (evalB_lit (by have := h σ hσ; omega))
        (h σ hσ)
  exact this.mono (by simp)

/-- **Two nested counted scans.** -/
theorem spec_scan2 (x m y k : String) (I J : Env → Prop) (N M Kb : ℕ) (hNB : N < B)
    (hMB : M < B) (hxN : ∀ σ, I σ → σ.vars x ≤ N) (hm : ∀ σ, I σ → σ.vars m = N)
    (hyM : ∀ σ, J σ → σ.vars y ≤ M) (hk : ∀ σ, J σ → σ.vars k = M)
    (hbody : Spec B (fun σ => J σ ∧ σ.vars y < M) c
      (fun σ σ' => J σ' ∧ σ'.vars y = σ.vars y + 1) Kb)
    (hin : ∀ σ, I σ → σ.vars x < N → J (σ.setVar y 0))
    (hout : ∀ σ σ', I σ → σ.vars x < N → J σ' → σ'.vars y = M →
      σ'.vars x = σ.vars x ∧ I (σ'.setVar x (σ'.vars x + 1))) :
    Spec B (fun σ => I (σ.setVar x 0)) (scan2 x m y k c)
      (fun _ σ' => I σ' ∧ σ'.vars x = N) (((Kb + 4) * M + 6 + 4 + 4) * N + 6) := by
  have hinner := ((Spec.forRangeZero y k J M Kb hMB hyM hk hbody).pre
    (P' := fun σ => I σ ∧ σ.vars x < N) fun σ h => hin σ h.1 h.2).post
    (Q' := fun σ σ' => I σ ∧ σ.vars x < N ∧ J σ' ∧ σ'.vars y = M)
    fun σ σ' hσ hq => ⟨hσ.1, hσ.2, hq⟩
  have hinc := spec_incr (B := B)
    (P := fun τ => ∃ σ, I σ ∧ σ.vars x < N ∧ J τ ∧ τ.vars y = M) x fun τ ⟨σ, hI, hx, hJ, hy⟩ => by
      have := (hout σ τ hI hx hJ hy).1; omega
  have hbody' := hinner.seq hinc (fun σ σ' _ hq => ⟨σ, hq⟩)
    (R := fun σ σ'' => I σ'' ∧ σ''.vars x = σ.vars x + 1)
    fun σ τ σ'' hσ hq hq' => by
      obtain ⟨hI, hx, hJ, hy⟩ := hq
      obtain ⟨heq, hI'⟩ := hout σ τ hI hx hJ hy
      subst hq'
      exact ⟨hI', by simp [heq]⟩
  exact Spec.forRangeZero x m I N ((Kb + 4) * M + 6 + 4) hNB hxN hm hbody'

end Lax434175Proofs.Cost
