import Lax434175.OperationsFamily
import Lax434175.BatchFamily
import Lax434175.ZooParameters
import Lax434175.Parameters
import Lax434175.Results
import Lax434175.Rejection
import Lax434175.MachineCovering
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Parameters of the zoo's results
type: definition
---
The parameters in which the zoo states results, as functions of the instances.

On the operations family and the batching family: the number $n$ of jobs, the
number $m$ of machines, the largest processing time $p_{\max}$ and weight
$w_{\max}$, the numbers $\#p$, $\#r$, $\#w$, $\#d$ of distinct processing times,
release dates, weights and due dates, the total weight $W$ and the total
processing time $P$. The processing time of an operation is its time on the
first machine, as in the field of processing times, and that of a job the sum
over its operations. A weight is $1$ and a due date $0$ when the objective has
none.

On the operations family also:

- the number of *kinds* of machines (Knop and Koutecký): machines of one kind
  have the same processing time for every operation, so this is the number of
  distinct columns of the matrix $(p_{ij})$;
- the *rank* of that matrix over the rationals (Chen, Marx, Ye and Zhang);
- $q_{\max}$, the largest processing time of the last operation of a job (and the
  predicate that every job has a last operation of positive length), and
  $\chi$, the largest number of jobs whose last operations, ending at their due
  dates, overlap at one instant — for jobs completed just in time the
  intervals $[d_j - q_j, d_j)$ (Heeger, Hermelin, Itzhaki, Schieber and
  Shabtay; $\omega$ there);
- the largest communication delay $c$;
- the speed ratio $s_{\max}/s_{\min}$ of uniform machines, the least over the
  speeds that represent the instance;
- the width of the precedence order, the largest number of pairwise
  incomparable jobs;
- the number $\tau$ of forbidden times, the instants at which no job may start
  or end;
- $n_{\max}$, the largest number of operations of a job;
- the number $g$ of batches into which batch setups group the jobs;
- with the threshold $D$: the gap $D - \mathrm{LP}$ to the optimum
  $\mathrm{LP}$ of the linear relaxation [CS-LP] of the vertex-cover formulation
  of Correa and Schulz, as in Ambühl and Mastrolilli (2009). With $P$ the
  transitive closure of the precedence relation and $i \parallel j$ for
  different jobs related in neither direction, it minimizes
  $\sum_j p_jw_j + \sum_{(i,j) \in P} p_iw_j + \sum_{i \parallel j} \delta_{ij}p_iw_j$
  over $\delta \ge 0$ with $\delta_{ij} + \delta_{ji} \ge 1$ for $i \parallel j$,
  $\delta_{ik} + \delta_{kj} \ge 1$ for $(i, j) \in P$, $j \parallel k$,
  $k \parallel i$, and $\delta_{il} + \delta_{kj} \ge 1$ for $(i, j), (k, l) \in P$,
  $j \parallel k$, $l \parallel i$. Its optimum equals those of the
  relaxations of Potts and of Chudak and Hochbaum (their Theorems 2 to 4); the
  parameter is $\lceil D - \mathrm{LP} \rceil$, and $0$ when negative;
- with the threshold $D$: the time window of job $j$ runs from its release date
  to its deadline, and also ends at $D$ for the makespan and at $d_j + D$ for the
  maximum lateness, since the decision version asks for that. The pathwidth
  $\mathrm{pw}(I)$ of the interval graph of the windows is the largest number of
  windows containing one instant, minus one, and the maximum slack is the largest
  window length minus processing time (Hanen and Munier Kordon). A window without
  end has length $0$ here; it occurs only without deadlines and with another
  objective.

On the batching family also $\mathrm{pw}(I)$ and the maximum slack, with the
same windows.

On single-machine scheduling with rejection: $n$, $\#p$, $p_{\max}$, the number
$\#e$ of distinct rejection costs, the largest rejection cost $e_{\max}$, and the
number of accepted jobs, read as an instance quantity: the least number of jobs
a feasible solution accepts, $n$ minus the most jobs whose rejection costs fit
the budget. On $P \mid\mid C_{\min}$: $n$ and $m$.
-/

namespace Lax434175.ResultParameters
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Parameters
open Lax434175.Results

/-- The sum of two parameters. -/
def plus {P : Problem} (κ κ' : Parameter P) : Parameter P := fun x => κ x + κ' x

/-- The largest number of the intervals `[a i, b i)` that contain one instant. -/
noncomputable def overlap {n : ℕ} (a b : Fin n → ℕ∞) : ℕ :=
  sSup {k | ∃ t : ℕ, k = (Finset.univ.filter fun j => a j ≤ t ∧ (t : ℕ∞) < b j).card}

namespace Ops

variable (s : Spec OperationsFamily.family)

/-- The number of jobs. -/
def n : Parameter (problem _ s) := fun x => x.base.jobs

/-- The number of machines. -/
def m : Parameter (problem _ s) := fun x => x.base.machines

/-- The largest processing time of an operation. -/
def pmax : Parameter (problem _ s) := fun x =>
  Finset.univ.sup fun o : Operations.Op x.base => Operations.opTime x.base o

/-- The number of distinct processing times of operations. -/
def numP : Parameter (problem _ s) := fun x =>
  (Finset.univ.image fun o : Operations.Op x.base => Operations.opTime x.base o).card

/-- The number of distinct release dates. -/
def numR : Parameter (problem _ s) := fun x => ZooParameters.distinct x.base.r

/-- The number of distinct weights. -/
def numW : Parameter (problem _ s) := fun x =>
  ZooParameters.weights Operations.kernel s.objective x.base x.objectiveData

/-- The number of distinct due dates. -/
def numD : Parameter (problem _ s) := fun x =>
  ZooParameters.dueDates Operations.kernel s.objective x.base x.objectiveData

/-- The weight of a job. -/
def weight (x : Inst _ s) (j : Fin x.base.jobs) : ℕ :=
  Objectives.weight (K := Operations.kernel) s.objective x.objectiveData j

/-- The due date of a job. -/
def due (x : Inst _ s) (j : Fin x.base.jobs) : ℕ :=
  Objectives.dueDate (K := Operations.kernel) s.objective x.objectiveData j

/-- The largest weight. -/
def wmax : Parameter (problem _ s) := fun x => Finset.univ.sup (weight s x)

/-- The total weight. -/
def totalW : Parameter (problem _ s) := fun x => ∑ j, weight s x j

/-- The processing time of a job: the sum over its operations. -/
def ptime (x : Operations.Inst) (j : Fin x.jobs) : ℕ :=
  ∑ k : Fin (x.ops j), Operations.opTime x ⟨j, k⟩

/-- The total processing time. -/
def totalP : Parameter (problem _ s) := fun x => ∑ j, ptime x.base j

/-- The number of kinds of machines: distinct columns of the matrix of
processing times. -/
def kinds : Parameter (problem _ s) := fun x =>
  (Finset.univ.image fun i : Fin x.base.machines =>
    fun o : Operations.Op x.base => x.base.p o.1 o.2 i).card

/-- The rank of the matrix of processing times. -/
noncomputable def rank : Parameter (problem _ s) := fun x =>
  (Matrix.of fun (o : Operations.Op x.base) (i : Fin x.base.machines) =>
    (x.base.p o.1 o.2 i : ℚ)).rank

/-- The processing time of the last operation of a job, `0` without operations. -/
def lastTime (x : Operations.Inst) (j : Fin x.jobs) : ℕ :=
  if h : 0 < x.ops j then Operations.opTime x ⟨j, ⟨x.ops j - 1, by omega⟩⟩ else 0

/-- Every job has a last operation of positive length. -/
def lastPositive (x : (problem _ s).Inst) : Prop := ∀ j, 0 < lastTime x.base j

/-- `q_max`: the largest processing time of a last operation. -/
def qmax : Parameter (problem _ s) := fun x => Finset.univ.sup (lastTime x.base)

/-- `χ`: the largest number of jobs whose last operations, ending at their due
dates, overlap at one instant. -/
noncomputable def chi : Parameter (problem _ s) := fun x =>
  overlap (fun j => ((due s x j - lastTime x.base j : ℕ) : ℕ∞)) (fun j => (due s x j : ℕ∞))

/-- The largest communication delay. -/
noncomputable def cmax : Parameter (problem _ s) := fun x =>
  sSup {c | ∃ i j, CommunicationDelays.view (s.module .communicationDelays)
    (x.data .communicationDelays : CommunicationDelays.Data _ x.base.toPar) i j c}

/-- The speed ratio `s_max / s_min` of uniform machines: the least over the
speeds representing the instance. -/
noncomputable def speedRatio (x : Inst _ s) : ℝ :=
  sInf {r | ∃ (q : Operations.Op x.base → ℕ) (sp : Fin x.base.machines → ℕ),
    (∀ o i, 0 < sp i ∧ x.base.p o.1 o.2 i * sp i = q o) ∧
    ∀ i i', (sp i : ℝ) ≤ r * sp i'}

/-- The precedence relation of an instance. -/
def prec (x : Inst _ s) (i j : Fin x.base.jobs) : Prop :=
  (s.module .precedence).order.view (x.data .precedence).1 i j

/-- The width of the precedence order: the largest set of jobs no two of which
are related by the transitive closure. -/
noncomputable def width : Parameter (problem _ s) := fun x =>
  sSup {k | ∃ S : Finset (Fin x.base.jobs), S.card = k ∧
    ∀ i ∈ S, ∀ j ∈ S, ¬ Relation.TransGen (prec s x) i j}

/-- The end of the time window of a job with the threshold `D`: its deadline,
and also `D` for the makespan and `d_j + D` for the maximum lateness. -/
noncomputable def windowEnd (x : Inst _ s) (D : ℤ) (j : Fin x.base.jobs) : ℕ∞ :=
  min (Deadlines.view (K := Operations.kernel) (s.module .deadlines) (x.data .deadlines) j)
    (match s.objective with
      | .makespan => (D.toNat : ℕ∞)
      | .lmax => (((due s x j : ℤ) + D).toNat : ℕ∞)
      | _ => ⊤)

/-- `pw(I)`: the largest number of time windows containing one instant, minus
one. -/
noncomputable def pw : TParameter (problem _ s) := fun x D =>
  overlap (fun j => (x.base.r j : ℕ∞)) (windowEnd s x D) - 1

/-- The maximum slack: the largest window length minus processing time. -/
noncomputable def slackmax : TParameter (problem _ s) := fun x D =>
  Finset.univ.sup fun j => (windowEnd s x D j).toNat - ptime x.base j - x.base.r j

/-- `τ`: the number of forbidden times, the instants at which no job may start or end. -/
def tau : Parameter (problem _ s) := fun x =>
  (ForbiddenTimes.view (s.module .forbiddenTimes) (x.data .forbiddenTimes)).dedup.length

/-- `n_max`: the largest number of operations of a job. -/
def nmax : Parameter (problem _ s) := fun x => Finset.univ.sup x.base.ops

/-- `g`: the number of batches into which batch setups group the jobs. -/
def numBatches : Parameter (problem _ s) := fun x =>
  (Finset.univ.image fun j => ShopExtras.BatchSetups.batch (x := x.base.toShop)
    (s.module .batchSetups) (x.data .batchSetups) j).card

/-- Two different jobs related in neither direction by the precedence order. -/
def Incomparable (x : Inst _ s) (i j : Fin x.base.jobs) : Prop :=
  i ≠ j ∧ ¬ Relation.TransGen (prec s x) i j ∧ ¬ Relation.TransGen (prec s x) j i

/-- A feasible solution of [CS-LP] (Correa and Schulz; Ambühl and Mastrolilli 2009). -/
def CSFeasible (x : Inst _ s) (δ : Fin x.base.jobs → Fin x.base.jobs → ℝ) : Prop :=
  (∀ i j, 0 ≤ δ i j) ∧
  (∀ i j, Incomparable s x i j → 1 ≤ δ i j + δ j i) ∧
  (∀ i j k, Relation.TransGen (prec s x) i j → Incomparable s x j k → Incomparable s x k i →
    1 ≤ δ i k + δ k j) ∧
  (∀ i j k l, Relation.TransGen (prec s x) i j → Incomparable s x j k →
    Relation.TransGen (prec s x) k l → Incomparable s x l i → 1 ≤ δ i l + δ k j)

open Classical in
/-- The objective of [CS-LP]. -/
noncomputable def csValue (x : Inst _ s) (δ : Fin x.base.jobs → Fin x.base.jobs → ℝ) : ℝ :=
  ∑ j, (ptime x.base j * weight s x j : ℝ) +
    ∑ i, ∑ j, (if Relation.TransGen (prec s x) i j then (ptime x.base i * weight s x j : ℝ)
      else if Incomparable s x i j then δ i j * ptime x.base i * weight s x j else 0)

/-- The optimum of [CS-LP], a lower bound on the total weighted completion time
on one machine. -/
noncomputable def csLP (x : Inst _ s) : ℝ :=
  sInf (csValue s x '' {δ | CSFeasible s x δ})

/-- `D − LP`: the threshold minus the optimum of [CS-LP], rounded up, and `0`
when negative. -/
noncomputable def gapLP : TParameter (problem _ s) := fun x D => ⌈(D : ℝ) - csLP s x⌉₊

end Ops

namespace Batch

variable (s : Spec BatchFamily.family)

/-- The number of jobs. -/
def n : Parameter (problem _ s) := fun x => x.base.jobs

/-- The largest processing time. -/
def pmax : Parameter (problem _ s) := fun x => Finset.univ.sup x.base.p

/-- The number of distinct processing times. -/
def numP : Parameter (problem _ s) := fun x => ZooParameters.distinct x.base.p

/-- The number of distinct release dates. -/
def numR : Parameter (problem _ s) := fun x => ZooParameters.distinct x.base.r

/-- The number of distinct weights. -/
def numW : Parameter (problem _ s) := fun x =>
  ZooParameters.weights BatchFamily.kernel s.objective x.base x.objectiveData

/-- The number of distinct due dates. -/
def numD : Parameter (problem _ s) := fun x =>
  ZooParameters.dueDates BatchFamily.kernel s.objective x.base x.objectiveData

/-- The weight of a job. -/
def weight (x : Inst _ s) (j : Fin x.base.jobs) : ℕ :=
  Objectives.weight (K := BatchFamily.kernel) s.objective x.objectiveData j

/-- The largest weight. -/
def wmax : Parameter (problem _ s) := fun x => Finset.univ.sup (weight s x)

/-- The total weight. -/
def totalW : Parameter (problem _ s) := fun x => ∑ j, weight s x j

/-- The total processing time. -/
def totalP : Parameter (problem _ s) := fun x => ∑ j, x.base.p j

/-- The due date of a job. -/
def due (x : Inst _ s) (j : Fin x.base.jobs) : ℕ :=
  Objectives.dueDate (K := BatchFamily.kernel) s.objective x.objectiveData j

/-- The end of the time window of a job with the threshold `D`, as on the
operations family. -/
noncomputable def windowEnd (x : Inst _ s) (D : ℤ) (j : Fin x.base.jobs) : ℕ∞ :=
  min (Deadlines.view (K := BatchFamily.kernel) (s.module (.field .deadlines))
      (x.data (.field .deadlines)) j)
    (match s.objective with
      | .makespan => (D.toNat : ℕ∞)
      | .lmax => (((due s x j : ℤ) + D).toNat : ℕ∞)
      | _ => ⊤)

/-- `pw(I)`: the largest number of time windows containing one instant, minus
one. -/
noncomputable def pw : TParameter (problem _ s) := fun x D =>
  overlap (fun j => (x.base.r j : ℕ∞)) (windowEnd s x D) - 1

/-- The maximum slack: the largest window length minus processing time. -/
noncomputable def slackmax : TParameter (problem _ s) := fun x D =>
  Finset.univ.sup fun j => (windowEnd s x D j).toNat - x.base.p j - x.base.r j

end Batch

namespace Reject

/-- The number of jobs. -/
def n : Parameter Rejection.problem := fun x => x.jobs

/-- The number of distinct processing times. -/
def numP : Parameter Rejection.problem := fun x => ZooParameters.distinct x.p

/-- The largest processing time. -/
def pmax : Parameter Rejection.problem := fun x => Finset.univ.sup x.p

/-- The number of distinct rejection costs. -/
def numE : Parameter Rejection.problem := fun x => ZooParameters.distinct x.e

/-- The largest rejection cost. -/
def emax : Parameter Rejection.problem := fun x => Finset.univ.sup x.e

/-- The least number of jobs a feasible solution accepts: `n` minus the most
jobs whose rejection costs fit the budget. -/
noncomputable def accepted : Parameter Rejection.problem := fun x =>
  x.jobs - sSup {k | ∃ S : Finset (Fin x.jobs), S.card = k ∧ ∑ j ∈ S, x.e j ≤ x.budget}

end Reject

namespace Cover

/-- The number of jobs. -/
def n : Parameter MachineCovering.problem := fun x => x.jobs

/-- The number of machines. -/
def m : Parameter MachineCovering.problem := fun x => x.machines

end Cover

end Lax434175.ResultParameters
