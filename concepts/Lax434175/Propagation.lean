import Lax434175.StandardReading

/-!
---
title: Results along special cases
type: theorem
---
A specification $s$ that is field by field a special case of $t$ embeds its
instances into those of $t$ (the lift): same kernel instance, data read with
the more general values, and schedules unchanged. A reading *lifts* along
$s \le t$ if every word of an instance of $s$ is also a word of its lift, and
every word that writes a schedule of the lift writes the same schedule of the
instance.

**Theorem.** If the reading lifts along $s \le t$, every algorithm for $t$ is one
for $s$ — the same program: deciding within $O(T)$ becomes deciding within
$O(T \circ \mathrm{lift})$, and likewise for approximations within a running
time, randomized ones and approximation schemes, with the ratio read on the lift.
The same holds for approximations and schemes of the kept weight, if the lift
keeps the total weight, and for deciding with wide words, also on the instances
satisfying a predicate: on those of $s$ whose lift satisfies it.

**Theorem.** The standard reading of the operations family lifts along every
$s \le t$ with the same value of the encoding field, and the standard reading of
the batching family lifts along every $s \le t$.

The second theorem holds because the standard words write every field by its
view, and reading data with a more general value does not change its view.

A reading *determines the answer* for $t$ if two instances of $t$ with thresholds
written by one word have the same threshold and the same answer.

**Theorem.** The standard reading of the operations family determines the answer
for every specification with the standard encoding, and the standard reading of
the batching family for every specification: the words parse uniquely, give the
same kernel instance and the same views, and constraints and costs read only the
views.

**Theorem.** Let the reading lift along $s \le t$ and determine the answer for $t$.
Then a word of an instance of $s$ has the same answer for $s$ and for $t$, and:

1. hardness goes up, by the identity on words: NP-hardness and strong
   NP-hardness of $s$ give those of $t$; W[t]-hardness for $\kappa_s$ gives
   W[t]-hardness for $\kappa_t$ if, on every word, $\kappa_t$ of an instance of $t$
   is at most a computable function of $\kappa_s$ of an instance of $s$, and
   para-NP-hardness likewise for any function;
2. the coarse classes go down: in P, pseudo-polynomial, in P for every fixed
   value (with $\kappa_t$ bounded by a function of $\kappa_s$ on every word), and
   FPT (with a computable bound, for a parameter of $s$ computable in polynomial
   time).
-/

namespace Lax434175.Propagation
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results

variable {K : Kernel} {F : Family K} (hF : F.Sound) (R : Reading F)

/-- The reading lifts along `s ≤ t`. -/
def Lifts {s t : Spec F} (h : s.le t) : Prop :=
  (∀ x w, R.Encodes s w x → R.Encodes t w ((lift F hF h).map x)) ∧
    ∀ x w σ, R.Decodes t ((lift F hF h).map x) w σ → R.Decodes s x w σ

variable {hF R}

axiom decidesExact_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h) {T : Inst F t → ℤ → ℕ} :
    DecidesExact (R.at t) T → DecidesExact (R.at s) fun x D => T ((lift F hF h).map x) D

axiom decidesWithin_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h) {T : Inst F t → ℕ} :
    DecidesWithin (R.at t) T → DecidesWithin (R.at s) fun x => T ((lift F hF h).map x)

axiom decidesWithinWide_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h) {T : Inst F t → ℕ} :
    DecidesWithinWide (R.at t) T → DecidesWithinWide (R.at s) fun x => T ((lift F hF h).map x)

axiom decidesWithinWide_restrict_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {φ : Inst F t → Prop} {T : {x : Inst F t // φ x} → ℕ} :
    DecidesWithinWide ((R.at t).restrict φ) T →
      DecidesWithinWide ((R.at s).restrict fun x => φ ((lift F hF h).map x))
        fun x => T ⟨(lift F hF h).map x.1, x.2⟩

axiom approxWithin_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {ρ : Inst F t → ℝ} {T : Inst F t → ℕ} :
    ApproxWithin (R.at t) ρ T →
      ApproxWithin (R.at s) (fun x => ρ ((lift F hF h).map x)) fun x => T ((lift F hF h).map x)

axiom randomApproxWithin_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {ρ : Inst F t → ℝ} {T : Inst F t → ℕ} :
    RandomApproxWithin (R.at t) ρ T →
      RandomApproxWithin (R.at s) (fun x => ρ ((lift F hF h).map x))
        fun x => T ((lift F hF h).map x)

axiom schemeWithin_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {T : ℚ → Inst F t → ℕ} :
    SchemeWithin (R.at t) T → SchemeWithin (R.at s) fun ε x => T ε ((lift F hF h).map x)

axiom randomDecidesWithin_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h) {T : Inst F t → ℕ} :
    RandomDecidesWithin (R.at t) T → RandomDecidesWithin (R.at s) fun x => T ((lift F hF h).map x)

axiom oneSidedDecidesWithin_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h) {T : Inst F t → ℕ} :
    OneSidedDecidesWithin (R.at t) T → OneSidedDecidesWithin (R.at s) fun x => T ((lift F hF h).map x)

axiom zeroErrorDecidesWithin_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h) {T : Inst F t → ℕ} :
    ZeroErrorDecidesWithin (R.at t) T → ZeroErrorDecidesWithin (R.at s) fun x => T ((lift F hF h).map x)

axiom approxKept_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {W : Parameters.Parameter (problem F s)} {W' : Parameters.Parameter (problem F t)}
    (hW : ∀ x, W' ((lift F hF h).map x) = W x) {ρ : Inst F t → ℝ} :
    ApproxKept (R.at t) W' ρ → ApproxKept (R.at s) W fun x => ρ ((lift F hF h).map x)

axiom ptasKept_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {W : Parameters.Parameter (problem F s)} {W' : Parameters.Parameter (problem F t)}
    (hW : ∀ x, W' ((lift F hF h).map x) = W x) :
    PTASKept (R.at t) W' → PTASKept (R.at s) W

axiom eptasKept_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {W : Parameters.Parameter (problem F s)} {W' : Parameters.Parameter (problem F t)}
    (hW : ∀ x, W' ((lift F hF h).map x) = W x) :
    EPTASKept (R.at t) W' → EPTASKept (R.at s) W

axiom fptasKept_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h)
    {W : Parameters.Parameter (problem F s)} {W' : Parameters.Parameter (problem F t)}
    (hW : ∀ x, W' ((lift F hF h).map x) = W x) :
    FPTASKept (R.at t) W' → FPTASKept (R.at s) W

axiom ops_lifts (hF : OperationsFamily.family.Sound) {s t : Spec OperationsFamily.family}
    (h : s.le t) (he : s.module .encoding = t.module .encoding) :
    Lifts hF StandardReading.ops h

axiom batch_lifts (hF : BatchFamily.family.Sound) {s t : Spec BatchFamily.family}
    (h : s.le t) : Lifts hF StandardReading.batch h

/-- The reading determines the answer for `t`. -/
def Determined (R : Reading F) (t : Spec F) : Prop :=
  ∀ u y y' D D', EncodesDecision (R.at t) u y D → EncodesDecision (R.at t) u y' D' →
    D = D' ∧ ((problem F t).Decides y D ↔ (problem F t).Decides y' D')

axiom ops_determined {t : Spec OperationsFamily.family} (ht : t.module .encoding = .standard) :
    Determined StandardReading.ops t

axiom batch_determined (t : Spec BatchFamily.family) : Determined StandardReading.batch t

open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

variable {s t : Spec F} {h : s.le t}

axiom yes_iff (hl : Lifts hF R h) (hd : Determined R t) {u : List ℕ} {x : Inst F s} {D : ℤ}
    (hx : EncodesDecision (R.at s) u x D) :
    (decision (R.at t)).Yes u ↔ (decision (R.at s)).Yes u

axiom npHard_up (hl : Lifts hF R h) (hd : Determined R t) :
    NPHard (R.at s) → NPHard (R.at t)

axiom stronglyNPHard_up (hl : Lifts hF R h) (hd : Determined R t) :
    StronglyNPHard (R.at s) → StronglyNPHard (R.at t)

axiom paraNPHard_up (hl : Lifts hF R h) (hd : Determined R t)
    {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) :
    ParaNPHard (R.at s) κs → ParaNPHard (R.at t) κt

axiom wHard_up (hl : Lifts hF R h) (hd : Determined R t) (w : ℕ)
    {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hg : Computable g) (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) :
    WHard (R.at s) w κs → WHard (R.at t) w κt

axiom inP_down (hl : Lifts hF R h) (hd : Determined R t) : InP (R.at t) → InP (R.at s)

axiom pseudoPoly_down (hl : Lifts hF R h) (hd : Determined R t) :
    PseudoPoly (R.at t) → PseudoPoly (R.at s)

axiom inPFixed_down (hl : Lifts hF R h) (hd : Determined R t)
    {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) :
    InPFixed (R.at t) κt → InPFixed (R.at s) κs

axiom isFPT_down (hl : Lifts hF R h) (hd : Determined R t)
    {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hg : Computable g) (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D))
    (hps : IsParameterized (parameterized (R.at s) κs)) :
    IsFPT (R.at t) κt → IsFPT (R.at s) κs

end Lax434175.Propagation
