import Lax434175.WordProblems
import Lax434175.Online
import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_F3_NPHard
import Lax434930.PolynomialTime
import Lax434930.NondeterministicPolynomialTime
import Lax429075.CNF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: The kinds of results on scheduling problems
type: definition
---
A result on a scheduling problem is a statement about its decision version on
words, about algorithms that output schedules, or about online play. Such
statements depend on how instances and schedules are written, so they are made
relative to a reading of the problem: which words encode which instance, which
words write which schedule, and what an online scheduler sees at each time. A
reading of a family gives one for every specification. The results of the
literature are claims about the standard binary readings; here every result
is a proposition about a given reading.

Fix a reading and parameters $\kappa$: functions of the instance and the
threshold into the naturals (most depend on the instance only; some, such as the
pathwidth of time windows that end at the threshold, depend on both). The decision version on words: a word of an instance, then the sign
and absolute value of an integral threshold $D$, is a yes-instance if some
feasible schedule has cost at most $D$. Running times are those of the word RAM
(lax-496464, lax-808846).

**Exact algorithms and hardness.** *In P*: decided in time $c\,(|w|+1)^d$ in
the bit size $|w|$. *Pseudo-polynomial*: in time $c\,(M+1)^e(|w|+1)^d$, where
$M$ is the largest number of the word. *NP-hard*: `NPHardIn` of lax-496464;
*strongly NP-hard*: NP-hard on the words whose numbers are at most
$c\,(\text{length}+1)^d$. *In P (pseudo-polynomial) for every fixed value* of
$\kappa$; *FPT*, *W[t]-hard* (strongly: on such words), *para-NP-hard*: NP-hard
for one fixed value.

**Running times.** An algorithm can be stated with its exact running time, a
function $T$ of the instance (of $n$, $m$, $p_{\max}$, the total weight, …): one
program halts, writing the answer for the instance and the threshold, within
$c\,(T(x)+1)$ instructions on the word of every instance $x$, at every word length $\ell$ with $(|w| + M + 2)^c \le 2^\ell$, where $|w|$ is
the length of the word and $M$ its largest number — words of $O(\log)$ bits, as
on the word RAM of the literature. Deciding, approximating, approximating with
random bits and approximation schemes each have such a form; a submitted
algorithm is a program with a proof of one of them. Deciding can also be stated
without the constant: one program halts with the answer within exactly $T(x, D)$
instructions, a function of the instance and the threshold, at the same word lengths.

**Randomized deciding.** The program reads, after the word, at most $c\,(T(x)+1)$
random bits and halts within $c\,(T(x)+1)$ instructions on every choice of them.
With *bounded error* its answer is right for at least two thirds of the choices.
With *one-sided error* it never accepts a no-instance and accepts a yes-instance
for at least half of the choices. With *zero error* (Las Vegas) it is always
right and the bound $c\,(T(x)+1)$ holds for the number of instructions averaged
over the choices. Repetition turns any of these into error $2^{-k}$ at $k$ times
the cost, so the constants $2/3$ and $1/2$ are not essential.

**Approximation.** A ratio is a function $\rho$ of the instance into the reals.
A $\rho$-approximation is a polynomial-time program that on the word of an
instance with a feasible schedule writes the word of a feasible schedule
costing at most $\rho$ times every feasible schedule; for a maximization
problem, whose cost is the negative of its value, the value is at least $\rho$
times every value. A randomized one reads polynomially many random bits; every
choice gives a feasible schedule, the average cost is within the ratio, and
the running time is polynomial in the worst case or, for an expected-time
algorithm, on average over the bits. Approximations may be restricted to the
instances of a set. PTAS, EPTAS and FPTAS are as usual; inapproximability below
$\rho$ unless P = NP says that if P ≠ NP no $\rho'$-approximation exists for a
constant $\rho' < \rho$. An *additive* $\delta$-approximation writes a feasible
schedule costing at most every feasible cost plus $\delta$, a function of the
instance; an additive scheme does so with $\varepsilon\,\delta$ for every
$\varepsilon > 0$, in polynomial time for each fixed $\varepsilon$. A
*parameterized approximation scheme* for a parameter $\kappa$ is one program that
writes a $(1 + a/b)$-approximate schedule from the word of an instance followed
by $a, b$, in time $f(\kappa + b/a)\,(|w|+1)^d$.

**Running times and word size.** A running time, upper or lower, is stated with
short words, $\ell \ge c \log_2(|u| + M + 2)$; the classes keep the long words
of the registered notions and are reached from running times through the
transfer theorems. A lower bound is stated for the time plus the length of the
shortest word of the instance.

**Wide words.** An algorithm whose running time $T$ exceeds every polynomial may
need words that hold the address of every step, $c\,(T(x)+1) \le 2^\ell$ besides
the short words above; this is the standard assumption for such algorithms, whose
tables are as large as their running times. Deciding within $O(T)$ with wide words
asks the program to work only at those word lengths.

**Restrictions.** A result may hold on the instances satisfying a predicate
$\varphi$ only: it is then a result on the problem restricted to them, read with the
same words.

**Kept weight.** A problem that minimizes the weight of the jobs it rejects
(late, or not just in time) is read with the same instances, schedules and
costs when a source maximizes the weight it keeps. The kept weight of a
schedule is the total weight $W$ of the instance minus its cost. A
$\rho$-approximation of the kept weight, for $\rho \le 1$, writes a feasible
schedule that keeps at least $\rho$ times the weight of every feasible
schedule; schemes keep $1 - a/b$ times it. An online algorithm is
$\rho$-competitive for the kept weight, $\rho \ge 1$, if every feasible schedule
keeps at most $\rho$ times what the algorithm keeps plus a constant, the
convention of the sources on throughput.

**Kernels.** A kernelization for a parameter is a polynomial-time map on the
words of instances that keeps the answer and whose output has size (bit length)
and parameter at most $g(\kappa)$ for a computable $g$; a polynomial kernel has
$g$ polynomial.

**The exponential time hypothesis.** A formula is written as the number $n$ of
variables followed, for every clause, by its length and its literals, the
literal of variable $v$ being $2v+1$ if positive and $2v$ if negative. ETH: for
some $q > 0$ no program decides the satisfiability of formulas whose clauses have
three literals over variables below $n$ within $c\,2^{\lfloor n/q \rfloor}(|w|+1)^c$
instructions, at the word lengths above. A function $f$ is $o(g)$ if for every
rational $\varepsilon > 0$, eventually $f(k) \le \varepsilon\, g(k)$.

**Online.** A deterministic algorithm is $\rho$-competitive if it is
non-anticipative for the revelation and, for some additive constant, its cost is
at most $\rho$ times every feasible cost plus that constant; a randomized one is
a finite distribution over non-anticipative algorithms. A lower bound $\rho$
says that no algorithm is $\rho'$-competitive for $\rho' < \rho$.
-/

namespace Lax434175.Results
open Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Parameters
open Lax434175.WordProblems Lax434175.Online
open Lax808846.Ram Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

/-- Parameterized problems on words. -/
abbrev WP := Lax888481.ParameterizedComplexity.Problem

/-- A reading of a problem: words of instances, schedules from words, and what
an online scheduler sees. -/
structure PReading (P : Problem) where
  /-- The word encodes the instance. -/
  Encodes : List ℕ → P.Inst → Prop
  /-- The word writes the schedule of the instance. -/
  Decodes : (x : P.Inst) → List ℕ → P.Sched x → Prop
  /-- What is revealed over time. -/
  reveal : Revelation P

/-- A reading of a family. -/
structure Reading {K : Kernel} (F : Family K) where
  /-- The word encodes the instance. -/
  Encodes : (s : Spec F) → List ℕ → Inst F s → Prop
  /-- The word writes the schedule of the instance. -/
  Decodes : (s : Spec F) → (x : Inst F s) → List ℕ → (problem F s).Sched x → Prop
  /-- What is revealed over time. -/
  reveal : (s : Spec F) → Revelation (problem F s)

/-- The reading of the problem of one specification. -/
def Reading.at {K : Kernel} {F : Family K} (R : Reading F) (s : Spec F) :
    PReading (problem F s) :=
  ⟨R.Encodes s, R.Decodes s, R.reveal s⟩

/-- The reading of a problem on the instances satisfying `φ`: the same words. -/
def PReading.restrict {P : Problem} (R : PReading P) (φ : P.Inst → Prop) :
    PReading (P.restrict φ) where
  Encodes w x := R.Encodes w x.1
  Decodes x w σ := R.Decodes x.1 w σ
  reveal := ⟨fun x y t => R.reveal.same x.1 y.1 t, fun x y σ τ t => R.reveal.agree x.1 y.1 σ τ t⟩

/-- A parameter of the decision version: a function of the instance and the
threshold. -/
abbrev TParameter (P : Problem) := P.Inst → ℤ → ℕ

/-- A parameter of the instance, ignoring the threshold. -/
def lift {P : Problem} (κ : Parameter P) : TParameter P := fun x _ => κ x

/-- The sum of two parameters. -/
def tplus {P : Problem} (κ κ' : TParameter P) : TParameter P := fun x D => κ x D + κ' x D

variable {P : Problem} (R : PReading P)

-- Words

/-- The largest number of a word. -/
def maxEntry (w : List ℕ) : ℕ := w.foldr max 0

/-- The word presents the instance with the threshold. -/
def EncodesDecision (w : List ℕ) (x : P.Inst) (D : ℤ) : Prop :=
  ∃ y, w = y ++ [if D < 0 then 1 else 0, D.natAbs] ∧ R.Encodes y x

open Classical in
/-- The decision version with a parameter, as a parameterized problem on words. -/
noncomputable def parameterized (κ : TParameter P) : WP where
  Domain := {w | ∃ x D, EncodesDecision R w x D}
  Yes w := ∃ x D, EncodesDecision R w x D ∧ P.Decides x D
  param w := if h : ∃ x D, EncodesDecision R w x D then κ h.choose h.choose_spec.choose else 0

/-- The decision version on words. -/
noncomputable def decision : WP := parameterized R fun _ => 0

open Classical in
/-- The answer of a word, `[1]` or `[0]`. -/
noncomputable def answer (Q : WP) (w : List ℕ) : List ℕ := if Q.Yes w then [1] else [0]

/-- The problem on fewer words. -/
def restrict (Q : WP) (D : Set (List ℕ)) : WP where
  Domain := Q.Domain ∩ D
  Yes := Q.Yes
  param := Q.param

/-- The words whose numbers are polynomial in their length. -/
def Small (c d : ℕ) : Set (List ℕ) := {w | ∀ v ∈ w, v ≤ c * (w.length + 1) ^ d}

/-- The words of instances with parameter at most `k`. -/
def Upto (κ : TParameter P) (k : ℕ) : Set (List ℕ) :=
  {w | ∃ x D, EncodesDecision R w x D ∧ κ x D ≤ k}

-- Exact algorithms and hardness

/-- Decided in polynomial time. -/
def PolyDecides (Q : WP) : Prop := PolyTimeOn Q.Domain (answer Q)

/-- Decided in pseudo-polynomial time. -/
def PseudoPolyDecides (Q : WP) : Prop :=
  ∃ (p : Program) (c e d : ℕ),
    ComputesInFptTime p Q.Domain maxEntry (answer Q) (fun k => c * (k + 1) ^ e) d

/-- The problem is in P. -/
def InP : Prop := PolyDecides (decision R)

/-- The problem is solvable in pseudo-polynomial time. -/
def PseudoPoly : Prop := PseudoPolyDecides (decision R)

/-- The problem is NP-hard. -/
def NPHard : Prop := Lax496464.WH_F3_NPHard.NPHardIn (decision R)

/-- The problem is strongly NP-hard. -/
def StronglyNPHard : Prop :=
  ∃ c d, Lax496464.WH_F3_NPHard.NPHardIn (restrict (decision R) (Small c d))

/-- In P for every fixed value of the parameter. -/
def InPFixed (κ : TParameter P) : Prop :=
  ∀ k, PolyDecides (restrict (decision R) (Upto R κ k))

/-- Pseudo-polynomial for every fixed value of the parameter. -/
def PseudoPolyFixed (κ : TParameter P) : Prop :=
  ∀ k, PseudoPolyDecides (restrict (decision R) (Upto R κ k))

/-- Fixed-parameter tractable. -/
def IsFPT (κ : TParameter P) : Prop := parameterized R κ ∈ FPT

/-- W[t]-hard. -/
def WHard (t : ℕ) (κ : TParameter P) : Prop := Hard (W t) (parameterized R κ)

/-- Strongly W[t]-hard: W[t]-hard on the words whose numbers are polynomial in
their length. -/
def StronglyWHard (t : ℕ) (κ : TParameter P) : Prop :=
  ∃ c d, Hard (W t) (restrict (parameterized R κ) (Small c d))

/-- Para-NP-hard: NP-hard for one fixed value of the parameter. -/
def ParaNPHard (κ : TParameter P) : Prop :=
  ∃ k, Lax496464.WH_F3_NPHard.NPHardIn (restrict (decision R) (Upto R κ k))

/-- Strongly NP-hard for one fixed value of the parameter. -/
def StronglyParaNPHard (κ : TParameter P) : Prop :=
  ∃ k c d, Lax496464.WH_F3_NPHard.NPHardIn
    (restrict (decision R) (Upto R κ k ∩ Small c d))

-- Approximation

open Classical in
/-- The length of the shortest word of the instance, `0` if it has none. Lower
bounds on running times are stated for a time plus this length, so that they
cannot hold just because the input cannot be read. -/
noncomputable def inputSize (x : P.Inst) : ℕ := sInf {k | ∃ w, R.Encodes w x ∧ w.length = k}

/-- The instance has a feasible schedule. -/
def Solvable (x : P.Inst) : Prop := ∃ τ, P.feasible x τ

/-- `σ` is feasible and within the ratio of every feasible schedule. -/
def Within (ρ : ℝ) (x : P.Inst) (σ : P.Sched x) : Prop :=
  P.feasible x σ ∧ ∀ τ, P.feasible x τ → (P.cost x σ : ℝ) ≤ ρ * P.cost x τ

/-- For a maximization problem: `σ` is feasible and its value is at least `ρ`
times every value. -/
def WithinMax (ρ : ℝ) (x : P.Inst) (σ : P.Sched x) : Prop :=
  P.feasible x σ ∧ ∀ τ, P.feasible x τ → ρ * (-(P.cost x τ : ℝ)) ≤ -(P.cost x σ : ℝ)

/-- The output word, read on instance `x`, is a schedule within the ratio. -/
def Good (ρ : P.Inst → ℝ) (x : P.Inst) (out : List ℕ) : Prop :=
  ∃ σ, R.Decodes x out σ ∧ Within (ρ x) x σ

/-- The same for a maximization problem. -/
def GoodMax (ρ : P.Inst → ℝ) (x : P.Inst) (out : List ℕ) : Prop :=
  ∃ σ, R.Decodes x out σ ∧ WithinMax (ρ x) x σ

/-- All instances. -/
def univ : Set P.Inst := Set.univ

/-- A constant ratio. -/
def const (ρ : ℝ) : P.Inst → ℝ := fun _ => ρ

/-- A polynomial-time `ρ`-approximation on the instances of `S`. -/
def ApproxOn (S : Set P.Inst) (ρ : P.Inst → ℝ) : Prop :=
  ∃ A : List ℕ → List ℕ, PolyTimeOn {w | ∃ x ∈ S, R.Encodes w x} A ∧
    ∀ w x, R.Encodes w x → x ∈ S → Solvable x → Good R ρ x (A w)

/-- A polynomial-time `ρ`-approximation. -/
def Approx (ρ : P.Inst → ℝ) : Prop := ApproxOn R univ ρ

/-- A polynomial-time `ρ`-approximation for a maximization problem. -/
def ApproxMax (ρ : P.Inst → ℝ) : Prop :=
  ∃ A : List ℕ → List ℕ, PolyTimeOn {w | ∃ x, R.Encodes w x} A ∧
    ∀ w x, R.Encodes w x → Solvable x → GoodMax R ρ x (A w)

/-- A polynomial-time `ρ`-approximation for every fixed value of the parameter. -/
def ApproxFixed (κ : Parameter P) (ρ : P.Inst → ℝ) : Prop :=
  ∀ k, ApproxOn R {x | κ x ≤ k} ρ

/-- The random bits `r` as a word. -/
def bits {L : ℕ} (r : Fin L → Bool) : List ℕ := List.ofFn fun i => if r i then 1 else 0

/-- Every choice of the random bits gives a feasible schedule, and the average
cost is within the ratio. -/
def GoodOnAverage {L : ℕ} (ρ : ℝ) (x : P.Inst) (out : (Fin L → Bool) → List ℕ) : Prop :=
  ∃ σ : (Fin L → Bool) → P.Sched x,
    (∀ r, R.Decodes x (out r) (σ r) ∧ P.feasible x (σ r)) ∧
    ∀ τ, P.feasible x τ → (∑ r, (P.cost x (σ r) : ℝ)) / 2 ^ L ≤ ρ * P.cost x τ

/-- A randomized polynomial-time `ρ`-approximation: it reads `L(|w|)` random
bits, with `L` polynomial, and runs in polynomial time on every choice. -/
def RandomApprox (ρ : P.Inst → ℝ) : Prop :=
  ∃ (A : List ℕ → List ℕ) (L : ℕ → ℕ) (c e : ℕ), (∀ n, L n ≤ c * (n + 1) ^ e) ∧
    PolyTimeOn {u | ∃ w x, R.Encodes w x ∧ ∃ r : Fin (L (bitSize w)) → Bool, u = w ++ bits r} A ∧
    ∀ w x, R.Encodes w x → Solvable x →
      GoodOnAverage R (ρ x) x fun r : Fin (L (bitSize w)) → Bool => A (w ++ bits r)

/-- The word lengths a program may use on input `u`: `c` times the logarithm of
the length plus the largest number. -/
def WordOk (c : ℕ) (u : List ℕ) (ℓ : ℕ) : Prop := (u.length + maxEntry u + 2) ^ c ≤ 2 ^ ℓ

/-- A randomized `ρ`-approximation in expected polynomial time: averaged over
the random bits, the number of instructions is at most `c (|w|+1)^c`. -/
def RandomApproxExpected (ρ : P.Inst → ℝ) : Prop :=
  ∃ (p : Program) (c : ℕ) (L : ℕ → ℕ), (∀ n, L n ≤ c * (n + 1) ^ c) ∧
    ∀ w x, R.Encodes w x → Solvable x →
      ∃ out : (Fin (L w.length) → Bool) → List ℕ, GoodOnAverage R (ρ x) x out ∧
        ∀ ℓ, (∀ r : Fin (L w.length) → Bool, WordOk c (w ++ bits r) ℓ) →
          ∃ t : (Fin (L w.length) → Bool) → ℕ,
            (∀ r, RunsTo ℓ p ((w ++ bits r).length :: (w ++ bits r)) (out r) (t r)) ∧
            (∑ r, (t r : ℝ)) / 2 ^ L w.length ≤ c * (w.length + 1 : ℝ) ^ c

/-- A polynomial-time approximation scheme. -/
def PTAS : Prop := ∀ ε : ℚ, 0 < ε → Approx R (const (1 + ε))

/-- A PTAS for a maximization problem: value at least `1 - ε` times every
value. -/
def PTASMax : Prop := ∀ ε : ℚ, 0 < ε → ε < 1 → ApproxMax R (const (1 - ε))

/-- A PTAS for every fixed value of the parameter. -/
def PTASFixed (κ : Parameter P) : Prop :=
  ∀ k (ε : ℚ), 0 < ε → ApproxOn R {x | κ x ≤ k} (const (1 + ε))

/-- The words of instances followed by a precision `a / b`. -/
def WordsEps : Set (List ℕ) :=
  {u | ∃ w x, R.Encodes w x ∧ ∃ a b, 0 < a ∧ 0 < b ∧ u = w ++ [a, b]}

/-- One program writes a `(1 + a / b)`-approximate schedule from the word of an
instance followed by `a, b`. -/
def Scheme (A : List ℕ → List ℕ) : Prop :=
  ∀ w x (a b : ℕ), R.Encodes w x → 0 < a → 0 < b → Solvable x →
    Good R (const (1 + (a : ℝ) / b)) x (A (w ++ [a, b]))

/-- An efficient PTAS: time `f(b/a) · (|w|+1)^d`. -/
def EPTAS : Prop :=
  ∃ A, Scheme R A ∧ FptTimeOn (WordsEps R) (fun u => u.getLastD 0 / u.dropLast.getLastD 1 + 1) A

/-- A fully polynomial-time approximation scheme: time polynomial in `|w|` and
`b/a`. -/
def FPTAS : Prop :=
  ∃ A, Scheme R A ∧ ∃ (p : Program) (c e d : ℕ), ComputesInFptTime p (WordsEps R)
    (fun u => u.getLastD 0 / u.dropLast.getLastD 1 + 1) A (fun k => c * (k + 1) ^ e) d

/-- P ≠ NP. -/
def PneNP : Prop :=
  Lax434930.PolynomialTime.P ≠ Lax434930.NondeterministicPolynomialTime.NP

/-- No `ρ'`-approximation for a constant `ρ' < ρ` on the instances of `S`,
unless P = NP. -/
def NoApproxBelowOn (S : Set P.Inst) (ρ : ℝ) : Prop :=
  PneNP → ∀ ρ' : ℝ, ρ' < ρ → ¬ ApproxOn R S (const ρ')

/-- No `ρ'`-approximation for a constant `ρ' < ρ`, unless P = NP. -/
def NoApproxBelow (ρ : ℝ) : Prop := NoApproxBelowOn R univ ρ

/-- No PTAS unless P = NP (the consequence of APX-hardness). -/
def NoPTAS : Prop := PneNP → ¬ PTAS R

/-- `σ` is feasible and costs at most every feasible cost plus `δ`. -/
def WithinAdd (δ : ℝ) (x : P.Inst) (σ : P.Sched x) : Prop :=
  P.feasible x σ ∧ ∀ τ, P.feasible x τ → (P.cost x σ : ℝ) ≤ P.cost x τ + δ

/-- The output word, read on instance `x`, is a schedule within the additive error. -/
def GoodAdd (δ : P.Inst → ℝ) (x : P.Inst) (out : List ℕ) : Prop :=
  ∃ σ, R.Decodes x out σ ∧ WithinAdd (δ x) x σ

/-- A polynomial-time approximation with additive error `δ`. -/
def ApproxAdd (δ : P.Inst → ℝ) : Prop :=
  ∃ A : List ℕ → List ℕ, PolyTimeOn {w | ∃ x, R.Encodes w x} A ∧
    ∀ w x, R.Encodes w x → Solvable x → GoodAdd R δ x (A w)

/-- An additive approximation scheme: additive error `ε δ` for every `ε > 0`, in polynomial
time for each fixed `ε`. -/
def AddScheme (δ : P.Inst → ℝ) : Prop := ∀ ε : ℚ, 0 < ε → ApproxAdd R fun x => (ε : ℝ) * δ x

open Classical in
/-- The parameter of the instance a word followed by a precision writes, plus the inverse
precision `b / a`. -/
noncomputable def paramEps (κ : Parameter P) (u : List ℕ) : ℕ :=
  (if h : ∃ x, R.Encodes (u.dropLast.dropLast) x then κ h.choose else 0) +
    u.getLastD 0 / u.dropLast.getLastD 1 + 1

/-- A parameterized approximation scheme: time `f(κ + b/a) · (|w|+1)^d`. -/
def ParamScheme (κ : Parameter P) : Prop :=
  ∃ A, Scheme R A ∧ FptTimeOn (WordsEps R) (paramEps R κ) A

/-- A kernelization: a polynomial-time map on the words of instances with a threshold that
keeps the answer and the words, and whose output has size and parameter at most `g κ`. -/
def KernelWithin (κ : TParameter P) (g : ℕ → ℕ) : Prop :=
  ∃ K : List ℕ → List ℕ, PolyTimeOn (parameterized R κ).Domain K ∧
    ∀ w ∈ (parameterized R κ).Domain, K w ∈ (parameterized R κ).Domain ∧
      ((parameterized R κ).Yes w ↔ (parameterized R κ).Yes (K w)) ∧
      bitSize (K w) ≤ g ((parameterized R κ).param w) ∧
      (parameterized R κ).param (K w) ≤ g ((parameterized R κ).param w)

/-- A kernel: a kernelization for a computable `g`. -/
def HasKernel (κ : TParameter P) : Prop := ∃ g, Computable g ∧ KernelWithin R κ g

/-- A polynomial kernel: a kernelization with `g` polynomial. -/
def PolyKernel (κ : TParameter P) : Prop := ∃ c d : ℕ, KernelWithin R κ fun k => c * (k + 1) ^ d

-- Kept weight

/-- `σ` is feasible and keeps at least `ρ` times the weight every feasible
schedule keeps, the kept weight being the total weight minus the cost. -/
def WithinKept (total : Parameter P) (ρ : ℝ) (x : P.Inst) (σ : P.Sched x) : Prop :=
  P.feasible x σ ∧ ∀ τ, P.feasible x τ →
    ρ * ((total x : ℝ) - P.cost x τ) ≤ (total x : ℝ) - P.cost x σ

/-- The output word, read on instance `x`, is a schedule within the ratio of
the kept weight. -/
def GoodKept (total : Parameter P) (ρ : P.Inst → ℝ) (x : P.Inst) (out : List ℕ) : Prop :=
  ∃ σ, R.Decodes x out σ ∧ WithinKept total (ρ x) x σ

/-- A polynomial-time `ρ`-approximation of the kept weight, `ρ ≤ 1`. -/
def ApproxKept (total : Parameter P) (ρ : P.Inst → ℝ) : Prop :=
  ∃ A : List ℕ → List ℕ, PolyTimeOn {w | ∃ x, R.Encodes w x} A ∧
    ∀ w x, R.Encodes w x → Solvable x → GoodKept R total ρ x (A w)

/-- One program keeps `1 - a / b` times the optimal kept weight, from the word
of an instance followed by `a, b` with `a < b`. -/
def SchemeKept (total : Parameter P) (A : List ℕ → List ℕ) : Prop :=
  ∀ w x (a b : ℕ), R.Encodes w x → 0 < a → a < b → Solvable x →
    GoodKept R total (const (1 - (a : ℝ) / b)) x (A (w ++ [a, b]))

/-- A PTAS for the kept weight. -/
def PTASKept (total : Parameter P) : Prop :=
  ∀ ε : ℚ, 0 < ε → ε < 1 → ApproxKept R total (const (1 - ε))

/-- An efficient PTAS for the kept weight: time `f(b/a) · (|w|+1)^d`. -/
def EPTASKept (total : Parameter P) : Prop :=
  ∃ A, SchemeKept R total A ∧
    FptTimeOn (WordsEps R) (fun u => u.getLastD 0 / u.dropLast.getLastD 1 + 1) A

/-- An FPTAS for the kept weight: time polynomial in `|w|` and `b/a`. -/
def FPTASKept (total : Parameter P) : Prop :=
  ∃ A, SchemeKept R total A ∧ ∃ (p : Program) (c e d : ℕ), ComputesInFptTime p (WordsEps R)
    (fun u => u.getLastD 0 / u.dropLast.getLastD 1 + 1) A (fun k => c * (k + 1) ^ e) d

/-- A parameterized approximation scheme for the kept weight. -/
def ParamSchemeKept (total : Parameter P) (κ : Parameter P) : Prop :=
  ∃ A, SchemeKept R total A ∧ FptTimeOn (WordsEps R) (paramEps R κ) A

/-- No `ρ'`-approximation of the kept weight for a constant `ρ' > ρ`, unless
P = NP. -/
def NoApproxKeptAbove (total : Parameter P) (ρ : ℝ) : Prop :=
  PneNP → ∀ ρ' : ℝ, ρ < ρ' → ¬ ApproxKept R total (const ρ')

-- Running times

open Classical in
/-- The answer for an instance and a threshold: `[1]` if some feasible schedule
costs at most the threshold, `[0]` otherwise. -/
noncomputable def verdict (x : P.Inst) (D : ℤ) : List ℕ := if P.Decides x D then [1] else [0]

/-- One program decides the decision version within `O(T(x))` instructions: on
every word of an instance `x` with a threshold `D` it writes the answer for `x`
and `D`. -/
def DecidesWithin (T : P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ), ∀ u x D, EncodesDecision R u x D →
    ∀ ℓ, WordOk c u ℓ → ∃ t ≤ c * (T x + 1),
      RunsTo ℓ p (u.length :: u) (verdict x D) t

/-- One program decides the decision version within `T x D` instructions, with no
hidden constant: on every word of an instance `x` with a threshold `D` it writes the
answer within `T x D` steps of the word RAM. -/
def DecidesExact (T : P.Inst → ℤ → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ), ∀ u x D, EncodesDecision R u x D →
    ∀ ℓ, WordOk c u ℓ → ∃ t ≤ T x D, RunsTo ℓ p (u.length :: u) (verdict x D) t

/-- One program decides the decision version within `O(T(x))` instructions with wide
words: on every word of an instance `x` with a threshold `D`, at every word length `ℓ` with
`WordOk c u ℓ` and `c (T(x) + 1) ≤ 2 ^ ℓ`, it writes the answer for `x` and `D` within
`c (T(x) + 1)` instructions. This is the standard assumption for algorithms whose running
time exceeds a polynomial: a word holds the address of every step. -/
def DecidesWithinWide (T : P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ), ∀ u x D, EncodesDecision R u x D →
    ∀ ℓ, WordOk c u ℓ → c * (T x + 1) ≤ 2 ^ ℓ → ∃ t ≤ c * (T x + 1),
      RunsTo ℓ p (u.length :: u) (verdict x D) t

open Classical in
/-- The choices of `L` random bits for which `out` writes the answer for `x` and `D`. -/
noncomputable def rightChoices {L : ℕ} (x : P.Inst) (D : ℤ) (out : (Fin L → Bool) → List ℕ) : ℕ :=
  (Finset.univ.filter fun r => out r = verdict x D).card

/-- A randomized program decides the decision version with bounded error within
`O(T(x))` instructions: on the word of an instance `x` with a threshold `D`
followed by at most `O(T(x))` random bits, it halts within `O(T(x))`
instructions on every choice, and writes the answer for at least two thirds of
the choices. -/
def RandomDecidesWithin (T : P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ) (L : ℕ → ℕ), ∀ u x D, EncodesDecision R u x D →
    L u.length ≤ c * (T x + 1) ∧
    ∃ out : (Fin (L u.length) → Bool) → List ℕ,
      2 * 2 ^ L u.length ≤ 3 * rightChoices x D out ∧
      ∀ r ℓ, WordOk c (u ++ bits r) ℓ → ∃ t ≤ c * (T x + 1),
        RunsTo ℓ p ((u ++ bits r).length :: (u ++ bits r)) (out r) t

/-- The same with one-sided error: a no-instance is never accepted, and a
yes-instance is accepted for at least half of the choices. -/
def OneSidedDecidesWithin (T : P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ) (L : ℕ → ℕ), ∀ u x D, EncodesDecision R u x D →
    L u.length ≤ c * (T x + 1) ∧
    ∃ out : (Fin (L u.length) → Bool) → List ℕ,
      (∀ r, out r = verdict x D ∨ out r = [0]) ∧
      2 ^ L u.length ≤ 2 * rightChoices x D out ∧
      ∀ r ℓ, WordOk c (u ++ bits r) ℓ → ∃ t ≤ c * (T x + 1),
        RunsTo ℓ p ((u ++ bits r).length :: (u ++ bits r)) (out r) t

/-- The same with zero error (Las Vegas): the answer is always right, and the
number of instructions, averaged over the choices, is `O(T(x))`. -/
def ZeroErrorDecidesWithin (T : P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ) (L : ℕ → ℕ), ∀ u x D, EncodesDecision R u x D →
    L u.length ≤ c * (T x + 1) ∧
    ∀ ℓ, (∀ r : Fin (L u.length) → Bool, WordOk c (u ++ bits r) ℓ) →
      ∃ t : (Fin (L u.length) → Bool) → ℕ,
        (∀ r, RunsTo ℓ p ((u ++ bits r).length :: (u ++ bits r)) (verdict x D) (t r)) ∧
        (∑ r, (t r : ℝ)) / 2 ^ L u.length ≤ c * ((T x : ℝ) + 1)

/-- A `ρ`-approximation running within `O(T(x))` instructions. -/
def ApproxWithin (ρ : P.Inst → ℝ) (T : P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ), ∀ u x, R.Encodes u x → Solvable x →
    ∀ ℓ, WordOk c u ℓ → ∃ out, ∃ t ≤ c * (T x + 1),
      RunsTo ℓ p (u.length :: u) out t ∧ Good R ρ x out

/-- A randomized `ρ`-approximation running within `O(T(x))` instructions on
every choice of random bits and reading at most that many. -/
def RandomApproxWithin (ρ : P.Inst → ℝ) (T : P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ) (L : ℕ → ℕ), ∀ u x, R.Encodes u x → Solvable x →
    L u.length ≤ c * (T x + 1) ∧
    ∃ out : (Fin (L u.length) → Bool) → List ℕ, GoodOnAverage R (ρ x) x out ∧
      ∀ r ℓ, WordOk c (u ++ bits r) ℓ → ∃ t ≤ c * (T x + 1),
        RunsTo ℓ p ((u ++ bits r).length :: (u ++ bits r)) (out r) t

/-- An approximation scheme: one program reads the word of an instance and `a, b`
and writes a `(1 + a/b)`-approximate schedule within `O(T(a/b, x))`
instructions. -/
def SchemeWithin (T : ℚ → P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ), ∀ u x (a b : ℕ), R.Encodes u x → 0 < a → 0 < b →
    Solvable x → ∀ ℓ, WordOk c (u ++ [a, b]) ℓ → ∃ out, ∃ t ≤ c * (T ((a : ℚ) / b) x + 1),
      RunsTo ℓ p ((u ++ [a, b]).length :: (u ++ [a, b])) out t ∧
      Good R (const (1 + (a : ℝ) / b)) x out

/-- The same for a maximization problem: value at least `1 - a/b` times every
value, for `a < b`. -/
def SchemeMaxWithin (T : ℚ → P.Inst → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ), ∀ u x (a b : ℕ), R.Encodes u x → 0 < a → a < b →
    Solvable x → ∀ ℓ, WordOk c (u ++ [a, b]) ℓ → ∃ out, ∃ t ≤ c * (T ((a : ℚ) / b) x + 1),
      RunsTo ℓ p ((u ++ [a, b]).length :: (u ++ [a, b])) out t ∧
      GoodMax R (const (1 - (a : ℝ) / b)) x out

-- The exponential time hypothesis

/-- The word of a formula on `n` variables. -/
def formulaWord (n : ℕ) (Φ : Lax429075.CNF.Formula) : List ℕ :=
  n :: Φ.flatMap fun C => C.length :: C.map fun l => 2 * l.index + if l.positive then 1 else 0

open Classical in
/-- The exponential time hypothesis: for some `q > 0`, no program decides 3-SAT
on `n` variables within `c · 2^⌊n/q⌋ · (|w|+1)^c` instructions. -/
def ETH : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∀ (p : Program) (c : ℕ), ¬ ∀ (n : ℕ) (Φ : Lax429075.CNF.Formula),
    (∀ C ∈ Φ, C.length = 3 ∧ ∀ l ∈ C, l.index < n) →
    ∀ ℓ, WordOk c (formulaWord n Φ) ℓ →
      ∃ t ≤ c * 2 ^ (n / q) * ((formulaWord n Φ).length + 1) ^ c,
        RunsTo ℓ p ((formulaWord n Φ).length :: formulaWord n Φ)
          (if Lax429075.CNF.Satisfiable Φ then [1] else [0]) t

/-- `f` is `o(g)`. -/
def LittleO (f g : ℕ → ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N, ∀ k ≥ N, (f k : ℚ) ≤ ε * g k

-- Online

/-- A deterministic algorithm with ratio `ρ` and additive constant `α`, over the
reals. -/
def CompetitiveR (A : Algorithm P) (ρ : P.Inst → ℝ) (α : ℝ) : Prop :=
  ∀ x, P.feasible x (A x) ∧ ∀ τ, P.feasible x τ →
    (P.cost x (A x) : ℝ) ≤ ρ x * P.cost x τ + α

/-- Some non-anticipative deterministic algorithm is `ρ`-competitive. -/
def DetCompetitive (ρ : P.Inst → ℝ) : Prop :=
  ∃ A α, NonAnticipative R.reveal A ∧ CompetitiveR A ρ α

/-- A distribution over non-anticipative algorithms is `ρ`-competitive. -/
def RandCompetitive (ρ : P.Inst → ℝ) : Prop :=
  ∃ (μ : Randomized R.reveal) (α : ℝ), ∀ x,
    (∀ a ∈ μ.algorithms, P.feasible x (a.2 x)) ∧
    ∀ τ, P.feasible x τ → (μ.cost x : ℝ) ≤ ρ x * P.cost x τ + α

/-- No deterministic algorithm is `ρ'`-competitive for a constant `ρ' < ρ`. -/
def DetLowerBound (ρ : ℝ) : Prop := ∀ ρ' < ρ, ¬ DetCompetitive R (const ρ')

/-- No randomized algorithm is `ρ'`-competitive for a constant `ρ' < ρ`. -/
def RandLowerBound (ρ : ℝ) : Prop := ∀ ρ' < ρ, ¬ RandCompetitive R (const ρ')

/-- For some `c > 0`, no deterministic algorithm is `c f`-competitive. -/
def DetLowerBoundFn (f : P.Inst → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ¬ DetCompetitive R fun x => c * f x

/-- For some `c > 0`, no randomized algorithm is `c f`-competitive. -/
def RandLowerBoundFn (f : P.Inst → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ¬ RandCompetitive R fun x => c * f x

-- Online, kept weight

/-- A deterministic algorithm with ratio `ρ ≥ 1` and additive constant `α` for
the kept weight: every feasible schedule keeps at most `ρ` times what the
algorithm keeps, plus `α`. -/
def CompetitiveKeptR (total : Parameter P) (A : Algorithm P) (ρ : P.Inst → ℝ) (α : ℝ) : Prop :=
  ∀ x, P.feasible x (A x) ∧ ∀ τ, P.feasible x τ →
    (total x : ℝ) - P.cost x τ ≤ ρ x * ((total x : ℝ) - P.cost x (A x)) + α

/-- Some non-anticipative deterministic algorithm is `ρ`-competitive for the
kept weight. -/
def DetCompetitiveKept (total : Parameter P) (ρ : P.Inst → ℝ) : Prop :=
  ∃ A α, NonAnticipative R.reveal A ∧ CompetitiveKeptR total A ρ α

/-- A distribution over non-anticipative algorithms is `ρ`-competitive for the
kept weight, in expectation. -/
def RandCompetitiveKept (total : Parameter P) (ρ : P.Inst → ℝ) : Prop :=
  ∃ (μ : Randomized R.reveal) (α : ℝ), ∀ x,
    (∀ a ∈ μ.algorithms, P.feasible x (a.2 x)) ∧
    ∀ τ, P.feasible x τ → (total x : ℝ) - P.cost x τ ≤ ρ x * ((total x : ℝ) - μ.cost x) + α

/-- No deterministic algorithm is `ρ'`-competitive for the kept weight, for a
constant `ρ' < ρ`. -/
def DetLowerBoundKept (total : Parameter P) (ρ : ℝ) : Prop :=
  ∀ ρ' < ρ, ¬ DetCompetitiveKept R total (const ρ')

/-- No randomized algorithm is `ρ'`-competitive for the kept weight, for a
constant `ρ' < ρ`. -/
def RandLowerBoundKept (total : Parameter P) (ρ : ℝ) : Prop :=
  ∀ ρ' < ρ, ¬ RandCompetitiveKept R total (const ρ')

/-- For some `c > 0`, no deterministic algorithm is `c f`-competitive for the
kept weight. -/
def DetLowerBoundFnKept (total : Parameter P) (f : P.Inst → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ¬ DetCompetitiveKept R total fun x => c * f x

/-- For some `c > 0`, no randomized algorithm is `c f`-competitive for the kept
weight. -/
def RandLowerBoundFnKept (total : Parameter P) (f : P.Inst → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ¬ RandCompetitiveKept R total fun x => c * f x

end Lax434175.Results
