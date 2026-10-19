import Lax888481.ParameterizedComplexity
import Lax496464.WH_A2_FptReductions
import Lax434175.Parameters

/-!
---
title: Scheduling problems as parameterized problems on words
type: theorem
---
A parameterized problem on words consists of the words that encode an
instance, the yes-instances among them, and a parameter read off the word.
Fixed-parameter tractability, fpt-reductions and hardness for a class of such
problems are those of the word RAM.

A coding of a family of scheduling problems says, for every specification,
which words encode which instance, such that a word encodes at most one
instance of a specification and a word that encodes an instance also encodes
it when the instance is read with a field-wise more general specification.

Given a coding, a specification $s$ and a parameter $\kappa$ of its problem,
the decision version of the problem of $s$ becomes a parameterized problem on
words. An instance $x$ with the integral threshold $D$ is encoded by a word
of $x$ followed by two entries, $1$ or $0$ according to whether $D$ is
negative, and $|D|$. The admissible words are these, the yes-instances are
those for which some feasible schedule has cost at most $D$, and the
parameter of the word is $\kappa(x)$.

**Theorem.** Let the fields of the family be sound, let $s$ be field by field
a special case of $t$, and let $\kappa_s$ and $\kappa_t$ be parameters with
$\kappa_t(x') \le g(\kappa_s(x))$ for a computable $g$ and every instance $x$
of $s$ read as an instance $x'$ of $t$. Then the parameterized problem of $s$
and $\kappa_s$ fpt-reduces to that of $t$ and $\kappa_t$; the reduction is
the identity on words. In particular this holds, with the same parameter on
both sides, for every parameter of the kernel instance and for every
invariant parameter of a constraint field. Consequently fixed-parameter
tractability passes from the problem of $t$ to that of $s$, and hardness for
a class from the problem of $s$ to that of $t$.
-/

namespace Lax434175.WordProblems
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.Parameters
open Lax496464.WH_A2_FptReductions
open scoped Lax496464.WH_A2_FptReductions

/-- A coding of the instances of the problems of a family by words. -/
structure Coding {K : Kernel} (F : Family K) where
  /-- The word encodes the instance. -/
  Encodes : (s : Spec F) → List ℕ → Inst F s → Prop
  /-- A word encodes at most one instance. -/
  unique : ∀ (s : Spec F) (w : List ℕ) (x y : Inst F s), Encodes s w x → Encodes s w y → x = y
  /-- A word of an instance is a word of the instance read with a more
  general specification. -/
  lift : ∀ (hF : F.Sound) {s t : Spec F} (h : s.le t) (w : List ℕ) (x : Inst F s),
    Encodes s w x → Encodes t w ((lift F hF h).map x)

variable {K : Kernel} {F : Family K}

/-- The word presents the instance together with the threshold: a word of the
instance followed by the sign and the absolute value of the threshold. -/
def EncodesDecision (C : Coding F) (s : Spec F) (w : List ℕ) (x : Inst F s) (D : ℤ) : Prop :=
  ∃ y, w = y ++ [if D < 0 then 1 else 0, D.natAbs] ∧ C.Encodes s y x

open Classical in
/-- The decision version of the problem of a specification, with a parameter,
as a parameterized problem on words. -/
noncomputable def wordProblem (C : Coding F) (s : Spec F) (κ : Parameter (problem F s)) :
    Lax888481.ParameterizedComplexity.Problem where
  Domain := {w | ∃ (x : Inst F s) (D : ℤ), EncodesDecision C s w x D}
  Yes w := ∃ (x : Inst F s) (D : ℤ), EncodesDecision C s w x D ∧ (problem F s).Decides x D
  param w := if h : ∃ (x : Inst F s) (D : ℤ), EncodesDecision C s w x D then κ h.choose else 0

axiom fptReduces_of_le (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κs : Parameter (problem F s)) (κt : Parameter (problem F t)) (g : ℕ → ℕ)
    (hg : Computable g) (hκ : ∀ x, κt ((lift F hF h).map x) ≤ g (κs x)) :
    wordProblem C s κs ≤ᶠᵖᵗ wordProblem C t κt

axiom fptReduces_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) :
    wordProblem C s (ofKernel F κ s) ≤ᶠᵖᵗ wordProblem C t (ofKernel F κ t)

axiom fptReduces_of_le_field (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (i : F.ModuleName) (κ : FieldParameter (F.module i)) (hκ : κ.Invariant) :
    wordProblem C s (ofField F i κ s) ≤ᶠᵖᵗ wordProblem C t (ofField F i κ t)

axiom fpt_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) :
    IsParameterized (wordProblem C s (ofKernel F κ s)) →
      wordProblem C t (ofKernel F κ t) ∈ FPT → wordProblem C s (ofKernel F κ s) ∈ FPT

axiom hard_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) (𝒞 : Set Lax888481.ParameterizedComplexity.Problem) :
    Hard 𝒞 (wordProblem C s (ofKernel F κ s)) → Hard 𝒞 (wordProblem C t (ofKernel F κ t))

end Lax434175.WordProblems
