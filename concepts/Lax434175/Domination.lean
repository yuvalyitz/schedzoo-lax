import Lax434175.ResultParameters

/-!
---
title: Results between parameters of one problem
type: theorem
---
A parameter $\kappa'$ of a problem is *dominated* by a parameter $\kappa$ if
$\kappa'(x, D) \le g(\kappa(x, D))$ for a function $g$ and every instance $x$ and
threshold $D$. Then the identity on words is an fpt-reduction from the problem
with $\kappa$ to the problem with $\kappa'$ when $g$ is computable, and the
words with $\kappa \le k$ are among those with $\kappa' \le g(0) + \dots + g(k)$.

**Theorem.** If $\kappa'$ is dominated by $\kappa$, then para-NP-hardness and
W[t]-hardness for $\kappa$ hold for $\kappa'$, and membership in XP and
fixed-parameter tractability for $\kappa'$ hold for $\kappa$ ($g$ computable for
the last two).

Two dominations of the zoo's parameters: a summand is dominated by a sum, and
on the operations family the number $\#p$ of distinct processing times is at
most $p_{\max} + 1$ (the values lie in $\{0, \dots, p_{\max}\}$).

**Theorem.** These dominations hold.
-/

namespace Lax434175.Domination
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters
open Lax496464.WH_A2_FptReductions

variable {P : Problem}

/-- `κ'` is bounded by `g` of `κ` on every instance and threshold. -/
def Dominated (κ' κ : TParameter P) (g : ℕ → ℕ) : Prop := ∀ x D, κ' x D ≤ g (κ x D)

axiom paraNPHard_of_dominated {R : PReading P} {κ κ' : TParameter P} {g : ℕ → ℕ}
    (h : Dominated κ' κ g) : ParaNPHard R κ → ParaNPHard R κ'

axiom wHard_of_dominated {R : PReading P} {κ κ' : TParameter P} {g : ℕ → ℕ} (t : ℕ)
    (hg : Computable g) (h : Dominated κ' κ g) : WHard R t κ → WHard R t κ'

axiom inPFixed_of_dominated {R : PReading P} {κ κ' : TParameter P} {g : ℕ → ℕ}
    (h : Dominated κ' κ g) : InPFixed R κ' → InPFixed R κ

axiom isFPT_of_dominated {R : PReading P} {κ κ' : TParameter P} {g : ℕ → ℕ}
    (hg : Computable g) (h : Dominated κ' κ g) (hp : IsParameterized (parameterized R κ)) :
    IsFPT R κ' → IsFPT R κ

axiom left_tplus (κ κ' : TParameter P) : Dominated κ (tplus κ κ') id

axiom right_tplus (κ κ' : TParameter P) : Dominated κ' (tplus κ κ') id

axiom ops_numP_pmax (s : Assembly.Spec OperationsFamily.family) :
    Dominated (lift (Ops.numP s)) (lift (Ops.pmax s)) (· + 1)

end Lax434175.Domination
