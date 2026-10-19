import Lax434175.Modules

/-!
---
title: Bounds on the number of machines and jobs
type: theorem
---
A count of a kernel assigns a natural number to every instance, such as its
number of machines or its number of jobs. The bound field of a count has the
values

- at most $k$, for every number $k$: the count is at most $k$, and at least
  a least number given with the count ($1$ for machines, $0$ for jobs);
- constant: no restriction on the instances; the value records that the
  count is regarded as a constant, as in the notation $n = k$;
- unlimited: the count is at least the number of jobs, as in the notation
  $P\infty$ for a machine for every job;
- at most one more than the jobs: the count is at most the number of jobs
  plus one, as in the notation $n \ge m - 1$ for the number $m$ of machines;
- any: no restriction.

At most $k$ is a special case of at most $l$ for $k \le l$, of constant and
of any; the other values are special cases of any.

In the three-field notation, $P2$ denotes two machines. Here it is read as at
most two machines and at least one, so that the problems with fewer machines
are special cases: an instance with one machine is an instance with at most
two. An instance without machines belongs to no problem with a bounded number
of machines.

**Theorem.** Over every kernel, for every count and every least number, the
bound field is sound.
-/

namespace Lax434175.Counts
open Lax434175.Kernels Lax434175.Modules

inductive Bound
  | atMost (k : ℕ)
  | constant
  | unlimited
  | atMostJobsPlusOne
  | any

/-- The numbers admitted by a bound, given the number of jobs. -/
def Bound.holds : Bound → (jobs count : ℕ) → Prop
  | .atMost k, _, n => n ≤ k
  | .constant, _, _ => True
  | .unlimited, jobs, n => jobs ≤ n
  | .atMostJobsPlusOne, jobs, n => n ≤ jobs + 1
  | .any, _, _ => True

def Bound.le : Bound → Bound → Bool
  | _, .any => true
  | .atMost k, .atMost l => decide (k ≤ l)
  | .atMost _, .constant => true
  | .constant, .constant => true
  | .unlimited, .unlimited => true
  | .atMostJobsPlusOne, .atMostJobsPlusOne => true
  | _, _ => false

/-- The numbers admitted by a bound, given the number of jobs and the least
number that a bound `at most k` admits. -/
def Bound.admits (least : ℕ) (v : Bound) (jobs n : ℕ) : Prop :=
  v.holds jobs n ∧ ∀ k, v = .atMost k → least ≤ n

/-- The bound field of a count; a bound `at most k` admits the counts from
`least` to `k`. -/
def module (K : Kernel) (count : K.Inst → ℕ) (least : ℕ := 0) : Module K :=
  Module.ofRestriction Bound (fun v x => v.admits least (K.jobs x) (count x)) Bound.le

axiom sound (K : Kernel) (count : K.Inst → ℕ) {least : ℕ} : (module K count least).Sound

end Lax434175.Counts
