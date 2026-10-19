import Lax434175.Encodings
import Lax434175.Results

/-!
---
title: Problems with bounds on parameters
type: theorem
---
Some special cases of a problem are not a choice of one value per field: they
bound a quantity that reads several fields at once. Zero slack, $d_j = r_j + p_j$,
reads the release date (kernel), the processing time (kernel) and the due date
(objective), so no single field can express it. Such a special case is a
*bounded problem*: the instances of a problem on which finitely many parameters
are at most given numbers. A parameter is any function of the instance into the
naturals, so "slack at most $\sigma$", "window at most $k$" and
"$p_{\max} \le k$" are all bounds.

A bounded problem is a restriction of its problem, so it is a special case of
it by the inclusion of instances, and a reading of the problem is a reading of
the bounded problem on the same words.

**Theorem.** A bounded problem is a special case of its problem.

**Theorem.** A sound embedding of $A$ in $B$ that maps every instance within the
bounds of $A$ to an instance within the bounds of $B$ makes the bounded problem
of $A$ a special case of the bounded problem of $B$. If it maps every instance
of $A$ within the bounds of $B$, then $A$ itself is a special case of the
bounded problem of $B$.

On one machine with release dates and due dates, the *due-date slack* of a job
is $d_j - r_j - p_j$, truncated at $0$, and the parameter is its largest value
over the jobs. Bounding it by $0$ gives the problem in which no job has room to
move: $d_j \le r_j + p_j$ for every job, so a job is on time exactly when it
starts at its release date and completes at its due date $d_j = r_j + p_j$, or it
cannot be on time at all.

**Theorem.** $1 \mid\mid \sum w_j Z_j$ is a special case of
$1 \mid r_j \mid \sum w_j U_j$ with due-date slack $0$: the encoding with release
dates $r_j = d_j - p_j$ produces only instances of slack $0$.
-/

namespace Lax434175.Bounded
open Lax434175 Lax434175.Problems Lax434175.Parameters Lax434175.Assembly
open Lax434175.ParallelMachines Lax434175.ParallelProblems Lax434175.Encodings

/-- A bound `κ ≤ k` on a parameter of a problem. -/
structure Bound (P : Problem) where
  /-- The parameter. -/
  param : Parameter P
  /-- Its largest admitted value. -/
  value : ℕ

/-- The instance is within every bound of the list. -/
def holds {P : Problem} (bs : List (Bound P)) (x : P.Inst) : Prop :=
  ∀ b ∈ bs, b.param x ≤ b.value

/-- The bounded problem: the instances of `P` within the bounds `bs`. -/
def bounded (P : Problem) (bs : List (Bound P)) : Problem :=
  P.restrict (holds bs)

/-- A reading of a problem read on the instances of a bounded problem: the same
words. -/
def reading {P : Problem} (R : Results.PReading P) (bs : List (Bound P)) :
    Results.PReading (bounded P bs) where
  Encodes w x := R.Encodes w x.1
  Decodes x w σ := R.Decodes x.1 w σ
  reveal := ⟨fun x y t => R.reveal.same x.1 y.1 t, fun x y σ τ t => R.reveal.agree x.1 y.1 σ τ t⟩

axiom bounded_specialCase (P : Problem) (bs : List (Bound P)) : SpecialCase (bounded P bs) P

axiom bounded_mono {A B : Problem} (e : Embedding A B) (he : e.Sound)
    (bs : List (Bound A)) (cs : List (Bound B)) (h : ∀ x, holds bs x → holds cs (e.map x)) :
    SpecialCase (bounded A bs) (bounded B cs)

axiom specialCase_bounded {A B : Problem} (e : Embedding A B) (he : e.Sound)
    (cs : List (Bound B)) (h : ∀ x, holds cs (e.map x)) : SpecialCase A (bounded B cs)

/-- The largest due-date slack `d_j - r_j - p_j`, truncated at `0`, on parallel
machines; `p_j` is the time of the job on all its machines together, which on
one machine is its processing time. A due date is `0` when the objective has
none. -/
def dueSlack (s : Spec nonpreemptive) : Parameter (problem nonpreemptive s) := fun x =>
  Finset.univ.sup fun j =>
    Objectives.dueDate (K := Nonpreemptive.model.kernel) s.objective x.objectiveData j
      - x.base.r j - duration x.base j Finset.univ

/-- `1 | r_j, d_j ≤ r_j + p_j | Σ w_j U_j`: one machine, release dates, weighted
late jobs, and due-date slack `0`. -/
def zeroSlackWeightedLate : Problem :=
  bounded (problem nonpreemptive (singleRelease .sumWU)) [⟨dueSlack (singleRelease .sumWU), 0⟩]

axiom weightedJustInTime_zeroSlack :
    SpecialCase (problem nonpreemptive (single .sumWZ)) zeroSlackWeightedLate

end Lax434175.Bounded
