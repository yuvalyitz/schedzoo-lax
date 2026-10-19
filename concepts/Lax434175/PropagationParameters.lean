import Lax434175.Propagation

/-!
---
title: Parameters along special cases
type: theorem
---
The transfers of parameterized results along a special case $s \le t$
(`Propagation`) ask that, on every word, the parameter of an instance of $t$ be at
most a function of the parameter of an instance of $s$. A parameter *agrees
along* $s \le t$ if, on every word, the two parameters are equal; then it is
bounded with the identity.

**Theorem.** Let $s \le t$ be specifications of the operations family, both with
the standard encoding. Under the standard reading the parameters $n$, $m$,
$p_{\max}$, $\#p$, $\#r$, $\#w$, $\#d$, $w_{\max}$, the number of kinds of
machines, the rank of $(p_{ij})$, $q_{\max}$, $\chi$, the largest communication
delay, the width of the precedence order, $pw(I)$ (the most time windows sharing an
instant, minus one) and the maximum slack agree along $s \le t$, and so do their
sums. The same holds for $n$, $p_{\max}$, $\#p$, $\#r$,
$\#w$, $\#d$ and $w_{\max}$ in the batching family.

The words determine the kernel instance, the views and the threshold, and the
lift changes none of them; every parameter listed reads only those. The time
window of a job ends at its deadline, and also at $D$ for the makespan and at
$d_j + D$ for the maximum lateness; the makespan is a special case only of
itself and of the maximum lateness with all due dates $0$, so the windows agree.

Fixed-parameter tractability in the sense of lax-496464 includes that the
parameter is computed in polynomial time. For a parameter that agrees along
$s \le t$, the parameter of a word of $s$ is that of the same word read for $t$,
so it is computed by the same program.

**Theorem.** If the reading lifts along $s \le t$ and determines the answer for
$t$, then fixed-parameter tractability goes down from $t$ to $s$ for every
parameter that agrees along $s \le t$.
-/

namespace Lax434175.PropagationParameters
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results
open Lax434175.ResultParameters

variable {K : Kernel} {F : Family K}

/-- On every word, the parameter of `t` equals that of `s`. -/
def WordEq (R : Reading F) {s t : Spec F} (κs : TParameter (problem F s))
    (κt : TParameter (problem F t)) : Prop :=
  ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' → κt y D' = κs x D

axiom wordEq_tplus {R : Reading F} {s t : Spec F} {κs κs' : TParameter (problem F s)}
    {κt κt' : TParameter (problem F t)} :
    WordEq R κs κt → WordEq R κs' κt' → WordEq R (tplus κs κs') (tplus κt κt')

/-- Fixed-parameter tractability goes down along `s ≤ t` for a parameter that agrees
on every word. -/
axiom isFPT_down_eq {hF : F.Sound} {R : Reading F} {s t : Spec F} {h : s.le t}
    (hl : Propagation.Lifts hF R h) (hd : Propagation.Determined R t)
    {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (hκ : WordEq R κs κt) :
    IsFPT (R.at t) κt → IsFPT (R.at s) κs

section Ops

variable {s t : Spec OperationsFamily.family}

axiom ops_n (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.n s)) (lift (Ops.n t))
axiom ops_m (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.m s)) (lift (Ops.m t))
axiom ops_pmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.pmax s)) (lift (Ops.pmax t))
axiom ops_numP (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numP s)) (lift (Ops.numP t))
axiom ops_numR (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numR s)) (lift (Ops.numR t))
axiom ops_kinds (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.kinds s)) (lift (Ops.kinds t))
axiom ops_rank (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.rank s)) (lift (Ops.rank t))
axiom ops_qmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.qmax s)) (lift (Ops.qmax t))
axiom ops_numW (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numW s)) (lift (Ops.numW t))
axiom ops_numD (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numD s)) (lift (Ops.numD t))
axiom ops_wmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.wmax s)) (lift (Ops.wmax t))
axiom ops_chi (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.chi s)) (lift (Ops.chi t))
axiom ops_cmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.cmax s)) (lift (Ops.cmax t))
axiom ops_width (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.width s)) (lift (Ops.width t))

axiom ops_pw (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (Ops.pw s) (Ops.pw t)
axiom ops_slackmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (Ops.slackmax s) (Ops.slackmax t)

end Ops

section Batch

variable {s t : Spec BatchFamily.family}

axiom batch_n (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.n s)) (lift (Batch.n t))
axiom batch_pmax (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.pmax s)) (lift (Batch.pmax t))
axiom batch_numP (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numP s)) (lift (Batch.numP t))
axiom batch_numR (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numR s)) (lift (Batch.numR t))
axiom batch_numW (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numW s)) (lift (Batch.numW t))
axiom batch_numD (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numD s)) (lift (Batch.numD t))
axiom batch_wmax (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.wmax s)) (lift (Batch.wmax t))

end Batch

end Lax434175.PropagationParameters
