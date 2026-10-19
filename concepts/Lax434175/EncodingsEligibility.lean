import Lax434175.ZooParallel
import Lax434175.Parameters
import Lax434175.StandardReading

/-!
---
title: Machine sets encoded by long processing times
type: theorem
---
On unrelated machines every processing time is finite, and the problems on
unrelated machines have no machine sets. A machine on which job $j$ may not run is instead encoded by a
processing time too long for every schedule within the threshold. Four
relations of the Scheduling Zoo rest on this encoding; each maps an instance
with machine sets $M_j$ and threshold $D$ to an instance on unrelated machines
with the same jobs, machines and times $p_{ij}$ for $i \in M_j$, and a long
time for $i \notin M_j$.

- $P \mid M_j \mid C_{\max}$ to $R \mid\mid C_{\max}$ and
  $Q \mid M_j \mid \sum C_j$ to $R \mid\mid \sum C_j$: the time $D + 1$. A job
  on a machine outside its set completes after $D$, so a schedule within the
  threshold uses only the machines of the sets, and it is a schedule of the
  instance with machine sets of the same cost. A job without a machine in its
  set makes both instances infeasible within the threshold.
- $P \mid M_j \mid \sum w_jC_j$ to $R \mid\mid \sum w_jC_j$: the time
  $D + 1$ again. A job of positive weight on a machine outside its set costs
  more than $D$; a job of weight $0$ costs nothing anywhere and is moved to
  the end of a machine of its set. An instance with a job whose set is empty
  is mapped to a threshold that no schedule meets.
- $P \mid M_j \mid \sum w_jZ_j$ to $R \mid\mid \sum w_jZ_j$: the time
  $d_j + 1$, so a job outside its set is never just in time; such jobs are
  moved to the end of a machine of their set, which makes no just-in-time job
  late. An instance with a job whose set is empty is mapped to a threshold
  that no schedule meets.

**Theorem.** The decision version of each of the four problems with machine
sets reduces to that of the problem on unrelated machines, with the same
numbers of jobs and machines.

The reduction is computed on the standard words: a program reads the word of an
instance with machine sets and its threshold and writes the word of the
unrelated instance and its threshold, in polynomial time and with numbers at
most one more than those it reads. So hardness goes up along the four
relations.

**Theorem.** Along each of the four relations, NP-hardness and strong
NP-hardness on the standard reading go from the problem with machine sets to the
problem on unrelated machines, and so does W[t]-hardness for the number of
machines.
-/

namespace Lax434175.EncodingsEligibility
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Parameters

/-- The numbers of jobs and machines of an instance. -/
def size {s : Spec OperationsFamily.family} (x : Inst OperationsFamily.family s) : ℕ × ℕ :=
  (x.base.jobs, x.base.machines)

/-- `P|Mj|Cmax` reduces to `R||Cmax`. -/
axiom machineSets_makespan :
    ReducibleWith (A := problem _ ZooParallel.p107) (B := problem _ ZooParallel.p5) size size
      (fun a b => b = a)

/-- `Q|Mj|ΣCj` reduces to `R||ΣCj`. -/
axiom machineSets_sumC :
    ReducibleWith (A := problem _ ZooParallel.p33) (B := problem _ ZooParallel.p31) size size
      (fun a b => b = a)

/-- `P|Mj|ΣwjCj` reduces to `R||ΣwjCj`. -/
axiom machineSets_sumWC :
    ReducibleWith (A := problem _ ZooParallel.p130) (B := problem _ ZooParallel.p222) size size
      (fun a b => b = a)

/-- `P|Mj|ΣwjZj` reduces to `R||ΣwjZj`. -/
axiom machineSets_sumWZ :
    ReducibleWith (A := problem _ ZooParallel.p200) (B := problem _ ZooParallel.p208) size size
      (fun a b => b = a)

open Lax434175.Results Lax434175.ResultParameters

/-- NP-hardness goes up along `P|Mj|Cmax → R||Cmax`. -/
axiom npHard_makespan :
    NPHard (StandardReading.ops.at ZooParallel.p107) → NPHard (StandardReading.ops.at ZooParallel.p5)

/-- NP-hardness goes up along `Q|Mj|ΣCj → R||ΣCj`. -/
axiom npHard_sumC :
    NPHard (StandardReading.ops.at ZooParallel.p33) → NPHard (StandardReading.ops.at ZooParallel.p31)

/-- NP-hardness goes up along `P|Mj|ΣwjCj → R||ΣwjCj`. -/
axiom npHard_sumWC :
    NPHard (StandardReading.ops.at ZooParallel.p130) → NPHard (StandardReading.ops.at ZooParallel.p222)

/-- NP-hardness goes up along `P|Mj|ΣwjZj → R||ΣwjZj`. -/
axiom npHard_sumWZ :
    NPHard (StandardReading.ops.at ZooParallel.p200) → NPHard (StandardReading.ops.at ZooParallel.p208)

/-- Strong NP-hardness goes up along `P|Mj|Cmax → R||Cmax`. -/
axiom stronglyNPHard_makespan :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p107) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p5)

/-- Strong NP-hardness goes up along `Q|Mj|ΣCj → R||ΣCj`. -/
axiom stronglyNPHard_sumC :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p33) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p31)

/-- Strong NP-hardness goes up along `P|Mj|ΣwjCj → R||ΣwjCj`. -/
axiom stronglyNPHard_sumWC :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p130) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p222)

/-- Strong NP-hardness goes up along `P|Mj|ΣwjZj → R||ΣwjZj`. -/
axiom stronglyNPHard_sumWZ :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p200) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p208)

/-- W[t]-hardness for the number of machines goes up along `P|Mj|Cmax → R||Cmax`. -/
axiom wHard_m_makespan (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p107) t (lift (Ops.m ZooParallel.p107)) →
      WHard (StandardReading.ops.at ZooParallel.p5) t (lift (Ops.m ZooParallel.p5))

/-- W[t]-hardness for the number of machines goes up along `Q|Mj|ΣCj → R||ΣCj`. -/
axiom wHard_m_sumC (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p33) t (lift (Ops.m ZooParallel.p33)) →
      WHard (StandardReading.ops.at ZooParallel.p31) t (lift (Ops.m ZooParallel.p31))

/-- W[t]-hardness for the number of machines goes up along `P|Mj|ΣwjCj → R||ΣwjCj`. -/
axiom wHard_m_sumWC (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p130) t (lift (Ops.m ZooParallel.p130)) →
      WHard (StandardReading.ops.at ZooParallel.p222) t (lift (Ops.m ZooParallel.p222))

/-- W[t]-hardness for the number of machines goes up along `P|Mj|ΣwjZj → R||ΣwjZj`. -/
axiom wHard_m_sumWZ (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p200) t (lift (Ops.m ZooParallel.p200)) →
      WHard (StandardReading.ops.at ZooParallel.p208) t (lift (Ops.m ZooParallel.p208))

end Lax434175.EncodingsEligibility
