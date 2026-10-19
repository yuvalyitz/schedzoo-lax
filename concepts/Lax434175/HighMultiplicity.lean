import Lax434175.Propagation
import Lax434175.ZooParallel

/-!
---
title: Standard words into high-multiplicity words
type: theorem
---
A high-multiplicity word lists every distinct job once, with its record, release
date, weight and due date, preceded by the number of jobs that have them
(`StandardReading`). It does not say which job is which, and it has no facts on
pairs of jobs.

**Theorem.** The standard reading determines the answer for every specification
with high multiplicity. Two instances written by one high-multiplicity word have
the same numbers of jobs and machines and the same global facts, and a bijection
between their jobs keeps every record, release date, weight and due date;
renaming the jobs along it maps the feasible schedules of one instance to those
of the other, at the same cost.

A program reads the standard word of an instance without facts on pairs of jobs
and writes the high-multiplicity word of the same instance: for every job it
counts the jobs with the same record, release date, weight and due date, and it
writes the distinct tuples in increasing order. It runs in polynomial time on
every word.

**Theorem.** Let $s \le t$, where $s$ has the standard encoding, no precedence
constraints and no communication delays, and $t$ has high multiplicity. Then
NP-hardness goes up from $s$ to $t$, and so does W[t]-hardness for parameters
$\kappa_s$ of $s$ and $\kappa_t$ of $t$, if on every instance written by a
high-multiplicity word of the lift of an instance $x$ of $s$, $\kappa_t$ is at
most a computable function of $\kappa_s(x)$. Being in P goes down from $t$ to
$s$, and so does fixed-parameter tractability under the same bound, for a
parameter of $s$ computable in polynomial time.

Strong NP-hardness is not carried: a high-multiplicity word can be much shorter
than the standard word of the same instance, so numbers that are small for the
standard word can be large for the high-multiplicity word.

**Theorem.** Along $P \mid\mid C_{\max} \to P \mid HM \mid C_{\max}$, NP-hardness
and W[t]-hardness for the number of machines go up, and fixed-parameter
tractability for the number of distinct processing times goes down. Here the
number of distinct processing times of $P \mid\mid C_{\max}$ is computed in
polynomial time by writing the high-multiplicity word and computing it there,
which fixed-parameter tractability of $P \mid HM \mid C_{\max}$ includes.
-/

namespace Lax434175.HighMultiplicity
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.ResultParameters
open Lax434175.Propagation

/-- The standard reading determines the answer for every specification with high
multiplicity. -/
axiom determined {t : Spec OperationsFamily.family}
    (ht : t.module .encoding = .highMultiplicity) : Determined StandardReading.ops t

/-- The arrow `s ≤ t` from a specification with the standard encoding and without
facts on pairs of jobs to one with high multiplicity. -/
structure Step (s t : Spec OperationsFamily.family) : Prop where
  le : s.le t
  standard : s.module .encoding = .standard
  highMultiplicity : t.module .encoding = .highMultiplicity
  noPrecedence : (s.module .precedence).order = .none
  noDelays : s.module .communicationDelays = .none

variable {s t : Spec OperationsFamily.family}

/-- On every instance `y` with threshold `D'` written by a high-multiplicity word of the
lift of an instance `x` of `s` with threshold `D`, `κt y D'` is at most `g (κs x D)`. -/
def ParamBound (hF : OperationsFamily.family.Sound) (h : s.le t) (κs : TParameter (problem _ s))
    (κt : TParameter (problem _ t)) (g : ℕ → ℕ) : Prop :=
  ∀ u x D y D', EncodesDecision (StandardReading.ops.at t) u ((Assembly.lift _ hF h).map x) D →
    EncodesDecision (StandardReading.ops.at t) u y D' → κt y D' ≤ g (κs x D)

open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

/-- NP-hardness goes up from the standard encoding to high multiplicity. -/
axiom npHard_up (hst : Step s t) :
    NPHard (StandardReading.ops.at s) → NPHard (StandardReading.ops.at t)

/-- W[t]-hardness goes up from the standard encoding to high multiplicity. -/
axiom wHard_up (hst : Step s t) (hF : OperationsFamily.family.Sound) (w : ℕ)
    {κs : TParameter (problem _ s)} {κt : TParameter (problem _ t)} (g : ℕ → ℕ) (hg : Computable g)
    (hκ : ParamBound hF hst.le κs κt g) :
    WHard (StandardReading.ops.at s) w κs → WHard (StandardReading.ops.at t) w κt

/-- Being in P goes down from high multiplicity to the standard encoding. -/
axiom inP_down (hst : Step s t) :
    InP (StandardReading.ops.at t) → InP (StandardReading.ops.at s)

/-- Fixed-parameter tractability goes down from high multiplicity to the standard
encoding. -/
axiom isFPT_down (hst : Step s t) (hF : OperationsFamily.family.Sound)
    {κs : TParameter (problem _ s)} {κt : TParameter (problem _ t)}
    (g : ℕ → ℕ) (hg : Computable g) (hκ : ParamBound hF hst.le κs κt g)
    (hps : IsParameterized (parameterized (StandardReading.ops.at s) κs)) :
    IsFPT (StandardReading.ops.at t) κt → IsFPT (StandardReading.ops.at s) κs

/-- NP-hardness goes up along `P||Cmax → P|HM|Cmax`. -/
axiom npHard_makespan :
    NPHard (StandardReading.ops.at ZooParallel.p0) → NPHard (StandardReading.ops.at ZooParallel.p254)

/-- W[t]-hardness for the number of machines goes up along `P||Cmax → P|HM|Cmax`. -/
axiom wHard_m_makespan (w : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p0) w (Results.lift (Ops.m ZooParallel.p0)) →
      WHard (StandardReading.ops.at ZooParallel.p254) w (Results.lift (Ops.m ZooParallel.p254))

/-- Fixed-parameter tractability for the number of distinct processing times goes down
along `P||Cmax → P|HM|Cmax`. -/
axiom isFPT_numP_makespan :
    IsFPT (StandardReading.ops.at ZooParallel.p254) (Results.lift (Ops.numP ZooParallel.p254)) →
      IsFPT (StandardReading.ops.at ZooParallel.p0) (Results.lift (Ops.numP ZooParallel.p0))

end Lax434175.HighMultiplicity
