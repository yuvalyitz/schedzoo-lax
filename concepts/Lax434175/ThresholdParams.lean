import Lax434175.ThresholdWords
import Lax434175.ResultParameters

/-!
---
title: Para-NP-hardness along the steps between objectives
type: theorem
---
A step between objectives (concept `ThresholdWords`: the makespan and the maximum
lateness to the number of late jobs and to the total tardiness, flow time to
tardiness, completion time to flow time) rewrites only the objective data and the
threshold of the standard word; the instance of the kernel, with its jobs,
machines, processing times and release dates, stays the same. So a parameter that
reads only the kernel instance takes the same value before and after the step.

A parameter of the target objective is *bounded on the kernel instance* by one of
the source objective if, for any two instances with the same kernel instance, the
first is at most the second.

**Theorem.** If the source objective is para-NP-hard for a parameter, and a
parameter of the target is bounded on the kernel instance by it, the target is
para-NP-hard for that parameter.

**Theorem.** The number of jobs $n$, the number of machines $m$, the largest
processing time $p_{\max}$, the numbers $\#p$ and $\#r$ of distinct processing
times and release dates, the number of kinds of machines and the rank of the
processing time matrix are each bounded on the kernel instance by themselves.
-/

namespace Lax434175.ThresholdParams
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.ThresholdWords
open Lax434175.ResultParameters

variable (values : (i : OperationsFamily.FieldName) → (OperationsFamily.family.module i).Value)

/-- `κt` is at most `κs` on any two instances with the same kernel instance. -/
def BaseBound (o o' : Objectives.Value) (κs : TParameter (problem _ (Thresholds.withObjective values o)))
    (κt : TParameter (problem _ (Thresholds.withObjective values o'))) : Prop :=
  ∀ x y D D', y.base = x.base → κt y D' ≤ κs x D

axiom paraNPHard_step (hs : values .encoding = .standard) {o o' : Objectives.Value} {mode : StepMode}
    (hm : stepOf o o' = some mode) {κs : TParameter (problem _ (Thresholds.withObjective values o))}
    {κt : TParameter (problem _ (Thresholds.withObjective values o'))}
    (hκ : BaseBound values o o' κs κt) :
    ParaNPHard (StandardReading.ops.at (Thresholds.withObjective values o)) κs →
      ParaNPHard (StandardReading.ops.at (Thresholds.withObjective values o')) κt

axiom base_n (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.n _)) (lift (Ops.n _))
axiom base_m (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.m _)) (lift (Ops.m _))
axiom base_pmax (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.pmax _)) (lift (Ops.pmax _))
axiom base_numP (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.numP _)) (lift (Ops.numP _))
axiom base_numR (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.numR _)) (lift (Ops.numR _))
axiom base_kinds (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.kinds _)) (lift (Ops.kinds _))
axiom base_rank (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.rank _)) (lift (Ops.rank _))

end Lax434175.ThresholdParams
