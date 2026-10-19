import Lax888481.Theorem3
import Lax434175.ParallelProblems

/-!
---
title: Interval scheduling with eligible machine sets as a zoo problem
type: theorem
---
An instance of interval scheduling with eligible machine sets has $n$ jobs and
$m$ machines; job $j$ has a processing time $1 \le p_j \le d_j$, a deadline
$d_j$, a weight $w_j$ and a set of eligible machines. A schedule runs some of
the jobs, each on an eligible machine during exactly $[d_j - p_j, d_j)$, such
that jobs on one machine do not overlap; the question is whether the
scheduled jobs can have weight at least $W$.

Read the same data as an instance of $P \mid M_j \mid \sum w_j Z_j$: identical
machines, job $j$ with processing time $p_j$, due date $d_j$, weight $w_j$ and
machine set the eligible machines. Here every job is scheduled, and the cost
is the total weight of the jobs that do not complete exactly at their due
date.

**Theorem.** If every job has an eligible machine, the interval scheduling
instance has a schedule of weight at least $W$ if and only if the zoo instance
has a schedule of cost at most $\sum_j w_j - W$.

The jobs completing at their due dates form the interval schedule; conversely
the jobs left out of an interval schedule are run one after another, on an
eligible machine each, after all due dates.

Encoding the zoo instance and threshold $\sum_j w_j - W$ by the word of the
interval scheduling instance and $W$, the zoo problem on the instances in
which every job has an eligible machine is a parameterized problem on words.

**Theorem.** This problem, parameterized by $m + p_{\max}$, is
fixed-parameter tractable.

An interval scheduling instance may have jobs without an eligible machine,
which no schedule runs. Padding the instance gives each of them one new
machine, eligible for them alone, and weight $0$; the other jobs keep their
data. The number of machines grows by one.

**Theorem.** Padding keeps the answer, and in the padded instance every job
has an eligible machine. Hence every interval scheduling instance with
threshold $W$ has the same answer as the zoo instance of its padding with
threshold $\sum_j w'_j - W$, where $w'$ are the padded weights.

Padding is computed on words by a word RAM program in one pass, linear in the
length of the word, and raises the number of machines by one.

**Theorem.** Interval scheduling with eligible machine sets, parameterized by
the number of machines, fpt-reduces to $P \mid M_j \mid \sum w_j Z_j$
parameterized by the number of machines.

Multicoloured Clique fpt-reduces to the former (Theorem 1 of lax-888481), so
composing the two reductions makes $P \mid M_j \mid \sum w_j Z_j$ W[1]-hard
for the number of machines; the composition of two such reductions is not
stated here.
-/

namespace Lax434175.IsemLink
open Lax434175 Lax434175.Problems Lax434175.Assembly
open Lax888481.Scheduling Lax888481.InstanceEncoding Lax888481.SchedulingProblems
open Lax888481.ParameterizedComplexity

/-- `P | M_j | Σ w_j Z_j` -/
def jitSets : Spec ParallelProblems.nonpreemptive :=
  ParallelProblems.spec _ .identical (machineSets := .sets) (objective := .sumWZ)

/-- The machine instance of an interval scheduling instance. -/
def base (I : Instance) : ParallelMachines.Inst where
  jobs := I.jobs
  machines := I.machines
  p := fun j _ => I.p j
  r := fun _ => 0

/-- The zoo instance of an interval scheduling instance. -/
def toZoo (I : Instance) : Inst ParallelProblems.nonpreemptive jitSets where
  base := base I
  data := fun i => by
    cases i
    · exact ()
    · exact ()
    · exact ()
    · exact ()
    · exact fun j i => i ∈ I.eligible j
    all_goals first | exact () | exact ((), ())
  admitted := fun i => by
    cases i
    · exact fun _ _ _ => rfl
    all_goals first | exact trivial | exact ⟨trivial, fun _ h => nomatch h⟩ | skip
    · exact fun _ => rfl
    all_goals first | exact trivial | exact ⟨fun _ _ h => h, trivial⟩
  objectiveData := (I.w, I.d)
  objectiveAdmitted := trivial

/-- The total weight of the jobs. -/
def totalWeight (I : Instance) : ℕ := ∑ j, I.w j

/-- Every job has an eligible machine. -/
def AllEligible (I : Instance) : Prop := ∀ j, (I.eligible j).Nonempty

axiom hasWeight_iff (I : Instance) (hI : AllEligible I) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ jitSets).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ)

/-- `P | M_j | Σ w_j Z_j` on the words of interval scheduling, for the
instances in which every job has an eligible machine, parameterized by the
number of machines plus the largest processing time. -/
def jitByMachinesAndPmax : Lax888481.ParameterizedComplexity.Problem where
  Domain := {x | ∃ I W, EncodesDecisionInstance x I W ∧ AllEligible I}
  Yes x := ∃ I W, EncodesDecisionInstance x I W ∧
    (problem _ jitSets).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ)
  param x := machineCount x + pmaxOf x

axiom fpt_jitByMachinesAndPmax : FPT jitByMachinesAndPmax

/-- `P | M_j | Σ w_j Z_j` on the words of interval scheduling, for the
instances in which every job has an eligible machine, parameterized by the
number of machines. -/
def jitByMachines : Lax888481.ParameterizedComplexity.Problem where
  Domain := {x | ∃ I W, EncodesDecisionInstance x I W ∧ AllEligible I}
  Yes x := ∃ I W, EncodesDecisionInstance x I W ∧
    (problem _ jitSets).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ)
  param x := machineCount x

/-- The padding of an interval scheduling instance: a job without an eligible
machine gets the new last machine and weight `0`. -/
def pad (I : Instance) : Instance where
  jobs := I.jobs
  machines := I.machines + 1
  p := I.p
  d := I.d
  w := fun j => if (I.eligible j).Nonempty then I.w j else 0
  eligible := fun j => if (I.eligible j).Nonempty then (I.eligible j).map Fin.castSuccEmb
    else {Fin.last I.machines}
  p_pos := I.p_pos
  p_le_d := I.p_le_d

axiom allEligible_pad (I : Instance) : AllEligible (pad I)

axiom hasWeight_pad (I : Instance) (W : ℕ) : I.HasWeight W ↔ (pad I).HasWeight W

axiom byMachines_fptReduces_jitByMachines : byMachines ≤fpt jitByMachines

axiom hasWeight_iff_zoo (I : Instance) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ jitSets).Decides (toZoo (pad I)) (((totalWeight (pad I) : ℤ) - W : ℤ) : ℚ)

end Lax434175.IsemLink
