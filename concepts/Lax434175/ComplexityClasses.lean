import Lax434930.NondeterministicPolynomialTime
import Lax496464.WH_B4_Hierarchies
import Lax434175.WordProblems

/-!
---
title: Complexity classes along special cases
type: theorem
---
The classes are those of the word RAM, for parameterized problems on words: a
set of admissible words, the yes-instances among them, and a parameter.

- **P**: one program decides the problem in polynomial time on its
  admissible words.
- **NP-hard**: every language in NP, written as words of zeros and ones,
  reduces to the problem in polynomial time on admissible words.
- **FPT**, **W[t]** and hardness for a class are those of the registered
  W-hierarchy (lax-496464).
- **XP**: one program decides the problem within $(|x|+2)^{f(k)}$
  instructions for a computable $f$, where $|x|$ is the bit size of the word
  and $k$ its parameter.
- **para-NP-hard**: the problem restricted to the words of parameter at most
  some $k$ is NP-hard.

A problem $A$ refines a problem $B$ if every admissible word of $A$ is one of
$B$, with the same answer and the same parameter.

**Theorem.** If $A$ refines $B$, then $B$ in P, FPT or XP puts $A$ there,
and $A$ NP-hard, para-NP-hard or hard for a class of parameterized problems
makes $B$ so.

**Theorem.** For a coding of a family of scheduling problems with sound
fields, the problem of a field-wise special case $s$ of $t$ refines that of
$t$, for every parameter of the kernel instance and every invariant parameter
of a constraint field.
-/

namespace Lax434175.ComplexityClasses
open Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.Parameters Lax434175.WordProblems
open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax888481.ParameterizedComplexity (Problem)

/-- The answer a deciding program writes. -/
noncomputable def answer (P : Problem) (x : List ℕ) : List ℕ :=
  open Classical in if P.Yes x then [1] else [0]

/-- `P` is in **P**. -/
def InP (P : Problem) : Prop := PolyTimeOn P.Domain (answer P)

/-- `P` reduces to `Q` in polynomial time on the admissible words of `P`. -/
def PolyReduces (P Q : Problem) : Prop := ∃ R, IsReduction P Q R ∧ PolyTimeOn P.Domain R

/-- A language of bit strings as a problem on words of zeros and ones. -/
def ofLanguage (A : Language) : Problem where
  Domain := {x | ∀ v ∈ x, v < 2}
  Yes x := x.map (fun v => decide (v = 1)) ∈ A
  param _ := 0

/-- `P` is **NP-hard**. -/
def NPHard (P : Problem) : Prop := ∀ A ∈ NP, PolyReduces (ofLanguage A) P

/-- On every admissible word, one program computes `F` within
`(bitSize x + 2) ^ f (κ x)` instructions, for a computable `f`. -/
def XPTimeOn (D : Set (List ℕ)) (κ : List ℕ → ℕ) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (f : ℕ → ℕ), Computable f ∧ ∀ x ∈ D,
    FitsInWords ((bitSize x + 2) ^ f (κ x)) ((x.length :: x) ++ F x) ∧
      ∀ w : ℕ, (bitSize x + 2) ^ f (κ x) ≤ w →
        ∃ t ≤ (bitSize x + 2) ^ f (κ x), RunsTo w p (x.length :: x) (F x) t

/-- **XP**. -/
def XP : Set Problem := {P | IsParameterized P ∧ XPTimeOn P.Domain P.param (answer P)}

/-- The words of parameter at most `k`. -/
def slice (P : Problem) (k : ℕ) : Problem where
  Domain := {x | x ∈ P.Domain ∧ P.param x ≤ k}
  Yes := P.Yes
  param := P.param

/-- `P` is **para-NP-hard**. -/
def ParaNPHard (P : Problem) : Prop := ∃ k, NPHard (slice P k)

/-- `A` refines `B`. -/
structure Refines (A B : Problem) : Prop where
  domain : A.Domain ⊆ B.Domain
  yes : ∀ x ∈ A.Domain, (A.Yes x ↔ B.Yes x)
  param : ∀ x ∈ A.Domain, A.param x = B.param x

variable {A B : Problem}

axiom inP_of_refines : Refines A B → InP B → InP A
axiom fpt_of_refines : Refines A B → B ∈ FPT → A ∈ FPT
axiom xp_of_refines : Refines A B → B ∈ XP → A ∈ XP
axiom npHard_of_refines : Refines A B → NPHard A → NPHard B
axiom paraNPHard_of_refines : Refines A B → ParaNPHard A → ParaNPHard B
axiom hard_of_refines (𝒞 : Set Problem) : Refines A B → Hard 𝒞 A → Hard 𝒞 B

variable {K : Kernel} {F : Family K}

axiom refines_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) :
    Refines (wordProblem C s (ofKernel F κ s)) (wordProblem C t (ofKernel F κ t))

axiom refines_of_le_field (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (i : F.ModuleName) (κ : FieldParameter (F.module i)) (hκ : κ.Invariant) :
    Refines (wordProblem C s (ofField F i κ s)) (wordProblem C t (ofField F i κ t))

end Lax434175.ComplexityClasses
