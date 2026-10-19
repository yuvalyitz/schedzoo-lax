import Lax434175.ZooParallel
import Lax434175.ZooParallelBatching
import Lax434175.ZooPreemptive
import Lax434175.ZooPreemptiveShops
import Lax434175.ZooSerialBatching
import Lax434175.ZooShops
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Open questions of The Scheduling Zoo
type: theorem
---
The 258 questions the zoo's data leaves open, each as two competing
propositions about a reading of the problem: `yes` and `no`. A question is posed
only where the data shows a gap: an open problem the zoo lists, a problem with
neither hardness nor an algorithm after carrying results along the arrows, an
NP-hard problem neither strongly hard nor pseudo-polynomial, or a parameter in XP
with neither fixed-parameter tractability nor hardness. Both sides of a question
cannot be proved unless P = NP, or W[t] = FPT for the parameterized questions
(`ZooOpen.exclusive_fpt`).
-/

namespace Lax434175.ZooOpen
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters
open Lax496464.WH_A2_FptReductions

/-- **Theorem.** Both sides of a parameterized question cannot hold unless every
parameterized problem of W[t] is fixed-parameter tractable. -/
axiom exclusive_fpt {P : Problem} {R : PReading P} {κ : TParameter P} {t : ℕ} :
    IsFPT R κ → WHard R t κ →
      ∀ Q ∈ Lax496464.WH_B4_Hierarchies.W t, IsParameterized Q →
        Q ∈ Lax496464.WH_A2_FptReductions.FPT

/-- `1||ΣwjTj`, parameter pmax: Is 1||ΣwjTj fixed-parameter tractable for the maximum processing time pmax? It is for agreeable weights and times, and 1|pj=p|ΣwjTj is polynomial.

The yes side. Source: open problem 1 of Mnich and van Bevern (2018).
-/
def ZooParallel_p133_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p133) (lift (Ops.pmax ZooParallel.p133))

/-- `1||ΣwjTj`, parameter pmax: Is 1||ΣwjTj fixed-parameter tractable for the maximum processing time pmax? It is for agreeable weights and times, and 1|pj=p|ΣwjTj is polynomial.

The no side. Source: open problem 1 of Mnich and van Bevern (2018).
-/
def ZooParallel_p133_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p133) 1 (lift (Ops.pmax ZooParallel.p133))

/-- `1|prec|ΣwjCj`, parameter D−LP: Does 1|prec|ΣwjCj have a polynomial kernel in the gap between the optimum and the lower bound of its natural LP relaxation? The problem is a special case of Weighted Vertex Cover, which has one.

The yes side. Source: open problem 2 of Mnich and van Bevern (2018).
-/
def ZooParallel_p15_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PolyKernel (R.at ZooParallel.p15) (Ops.gapLP ZooParallel.p15)

/-- `1|prec|ΣwjCj`, parameter D−LP: Does 1|prec|ΣwjCj have a polynomial kernel in the gap between the optimum and the lower bound of its natural LP relaxation? The problem is a special case of Weighted Vertex Cover, which has one.

The no side. Source: open problem 2 of Mnich and van Bevern (2018).
-/
def ZooParallel_p15_q0_no (R : Reading OperationsFamily.family) : Prop :=
  ¬ PolyKernel (R.at ZooParallel.p15) (Ops.gapLP ZooParallel.p15)

/-- `1|rj|ΣUj`, parameter pmax: Are 1|rj|ΣUj and 1|rj|ΣwjUj W[1]-hard for the maximum processing time pmax? Not even membership in XP is known.

The yes side. Source: open problem 3 of Mnich and van Bevern (2018).
-/
def ZooParallel_p252_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p252) (lift (Ops.pmax ZooParallel.p252))

/-- `1|rj|ΣUj`, parameter pmax: Are 1|rj|ΣUj and 1|rj|ΣwjUj W[1]-hard for the maximum processing time pmax? Not even membership in XP is known.

The no side. Source: open problem 3 of Mnich and van Bevern (2018).
-/
def ZooParallel_p252_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p252) 1 (lift (Ops.pmax ZooParallel.p252))

/-- `1|rj|ΣwjUj`, parameter pmax: Are 1|rj|ΣUj and 1|rj|ΣwjUj W[1]-hard for the maximum processing time pmax? Not even membership in XP is known.

The yes side. Source: open problem 3 of Mnich and van Bevern (2018).
-/
def ZooParallel_p237_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p237) (lift (Ops.pmax ZooParallel.p237))

/-- `1|rj|ΣwjUj`, parameter pmax: Are 1|rj|ΣUj and 1|rj|ΣwjUj W[1]-hard for the maximum processing time pmax? Not even membership in XP is known.

The no side. Source: open problem 3 of Mnich and van Bevern (2018).
-/
def ZooParallel_p237_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p237) 1 (lift (Ops.pmax ZooParallel.p237))

/-- `1|forbidden-times|Cmax`, parameter τ: Is makespan minimization on a single machine with τ forbidden start and end times fixed-parameter tractable for τ? It is solvable in time n^O(τ), and in polynomial time for constant τ even when the number of jobs of each length is written in binary.

The yes side. Source: open problem 4 of Mnich and van Bevern (2018).
-/
def ZooParallel_p253_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p253) (lift (Ops.tau ZooParallel.p253))

/-- `1|forbidden-times|Cmax`, parameter τ: Is makespan minimization on a single machine with τ forbidden start and end times fixed-parameter tractable for τ? It is solvable in time n^O(τ), and in polynomial time for constant τ even when the number of jobs of each length is written in binary.

The no side. Source: open problem 4 of Mnich and van Bevern (2018).
-/
def ZooParallel_p253_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p253) 1 (lift (Ops.tau ZooParallel.p253))

/-- `P|HM|Cmax`, parameter #p: Is P||Cmax with the high-multiplicity encoding fixed-parameter tractable for the number p̄ of distinct processing times? It is polynomial for constant p̄, and a fixed-parameter algorithm needs an output schedule that is not listed machine by machine.

The yes side. Source: open problem 5 of Mnich and van Bevern (2018).
-/
def ZooParallel_p254_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p254) (lift (Ops.numP ZooParallel.p254))

/-- `P|HM|Cmax`, parameter #p: Is P||Cmax with the high-multiplicity encoding fixed-parameter tractable for the number p̄ of distinct processing times? It is polynomial for constant p̄, and a fixed-parameter algorithm needs an output schedule that is not listed machine by machine.

The no side. Source: open problem 5 of Mnich and van Bevern (2018).
-/
def ZooParallel_p254_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p254) 1 (lift (Ops.numP ZooParallel.p254))

/-- `P3|prec;pj=1|Cmax`, parameter width: Is P3|prec;pj=1|Cmax fixed-parameter tractable for the width of the partial order? A negative answer settles a question of Garey and Johnson; the slight generalizations are W[2]-hard.

The yes side. Source: open problem 6 of Mnich and van Bevern (2018).
-/
def ZooParallel_p255_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p255) (lift (Ops.width ZooParallel.p255))

/-- `P3|prec;pj=1|Cmax`, parameter width: Is P3|prec;pj=1|Cmax fixed-parameter tractable for the width of the partial order? A negative answer settles a question of Garey and Johnson; the slight generalizations are W[2]-hard.

The no side. Source: open problem 6 of Mnich and van Bevern (2018).
-/
def ZooParallel_p255_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p255) 1 (lift (Ops.width ZooParallel.p255))

/-- `P|rj;pj=p|ΣwjUj`, parameter m: Are P|rj;pj=p|ΣwjUj and P|rj;pj=p|ΣUj fixed-parameter tractable for the number of machines? Their complexity is open when the number of machines is part of the input.

The yes side. Source: open problem 7 of Mnich and van Bevern (2018).
-/
def ZooParallel_p29_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p29) (lift (Ops.m ZooParallel.p29))

/-- `P|rj;pj=p|ΣwjUj`, parameter m: Are P|rj;pj=p|ΣwjUj and P|rj;pj=p|ΣUj fixed-parameter tractable for the number of machines? Their complexity is open when the number of machines is part of the input.

The no side. Source: open problem 7 of Mnich and van Bevern (2018).
-/
def ZooParallel_p29_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p29) 1 (lift (Ops.m ZooParallel.p29))

/-- `P|rj;pj=p|ΣUj`, parameter m: Are P|rj;pj=p|ΣwjUj and P|rj;pj=p|ΣUj fixed-parameter tractable for the number of machines? Their complexity is open when the number of machines is part of the input.

The yes side. Source: open problem 7 of Mnich and van Bevern (2018).
-/
def ZooParallel_p238_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p238) (lift (Ops.m ZooParallel.p238))

/-- `P|rj;pj=p|ΣUj`, parameter m: Are P|rj;pj=p|ΣwjUj and P|rj;pj=p|ΣUj fixed-parameter tractable for the number of machines? Their complexity is open when the number of machines is part of the input.

The no side. Source: open problem 7 of Mnich and van Bevern (2018).
-/
def ZooParallel_p238_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p238) 1 (lift (Ops.m ZooParallel.p238))

/-- `P|Mj|ΣwjZj`, parameter m: Is just-in-time scheduling on identical machines with machine sets (P|Mj;dj−rj=pj|ΣwjUj) fixed-parameter tractable for the number of machines? A positive answer would be a first step towards unrelated machines.

The yes side. Source: open problem 8 of Mnich and van Bevern (2018).
-/
def ZooParallel_p200_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p200) (lift (Ops.m ZooParallel.p200))

/-- `P|Mj|ΣwjZj`, parameter m: Is just-in-time scheduling on identical machines with machine sets (P|Mj;dj−rj=pj|ΣwjUj) fixed-parameter tractable for the number of machines? A positive answer would be a first step towards unrelated machines.

The no side. Source: open problem 8 of Mnich and van Bevern (2018).
-/
def ZooParallel_p200_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p200) 1 (lift (Ops.m ZooParallel.p200))

/-- `P|rj;pmtn|ΣCj`, parameter #p: Are the three NP-hard preemptive problems P|pmtn;rj|ΣCj, P|pmtn|ΣUj and P|pmtn|ΣTj fixed-parameter tractable for the number of distinct processing times? With equal processing times they are polynomial.

The yes side. Source: open problem 9 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p18_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p18) (lift (Ops.numP ZooPreemptive.p18))

/-- `P|rj;pmtn|ΣCj`, parameter #p: Are the three NP-hard preemptive problems P|pmtn;rj|ΣCj, P|pmtn|ΣUj and P|pmtn|ΣTj fixed-parameter tractable for the number of distinct processing times? With equal processing times they are polynomial.

The no side. Source: open problem 9 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p18_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p18) 1 (lift (Ops.numP ZooPreemptive.p18))

/-- `P|pmtn|ΣUj`, parameter #p: Are the three NP-hard preemptive problems P|pmtn;rj|ΣCj, P|pmtn|ΣUj and P|pmtn|ΣTj fixed-parameter tractable for the number of distinct processing times? With equal processing times they are polynomial.

The yes side. Source: open problem 9 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p45_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p45) (lift (Ops.numP ZooPreemptive.p45))

/-- `P|pmtn|ΣUj`, parameter #p: Are the three NP-hard preemptive problems P|pmtn;rj|ΣCj, P|pmtn|ΣUj and P|pmtn|ΣTj fixed-parameter tractable for the number of distinct processing times? With equal processing times they are polynomial.

The no side. Source: open problem 9 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p45_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p45) 1 (lift (Ops.numP ZooPreemptive.p45))

/-- `P|pmtn|ΣTj`, parameter #p: Are the three NP-hard preemptive problems P|pmtn;rj|ΣCj, P|pmtn|ΣUj and P|pmtn|ΣTj fixed-parameter tractable for the number of distinct processing times? With equal processing times they are polynomial.

The yes side. Source: open problem 9 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p74_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p74) (lift (Ops.numP ZooPreemptive.p74))

/-- `P|pmtn|ΣTj`, parameter #p: Are the three NP-hard preemptive problems P|pmtn;rj|ΣCj, P|pmtn|ΣUj and P|pmtn|ΣTj fixed-parameter tractable for the number of distinct processing times? With equal processing times they are polynomial.

The no side. Source: open problem 9 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p74_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p74) 1 (lift (Ops.numP ZooPreemptive.p74))

/-- `P2|pmtn;pj=p|ΣwjUj`, parameter pmax: Is P2|pmtn;pj=p|ΣwjUj W[1]-hard for the common processing time p?

The yes side. Source: open problem 10 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p75_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p75) (lift (Ops.pmax ZooPreemptive.p75))

/-- `P2|pmtn;pj=p|ΣwjUj`, parameter pmax: Is P2|pmtn;pj=p|ΣwjUj W[1]-hard for the common processing time p?

The no side. Source: open problem 10 of Mnich and van Bevern (2018).
-/
def ZooPreemptive_p75_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p75) 1 (lift (Ops.pmax ZooPreemptive.p75))

/-- `F3||Cmax`, parameter pmax: Is F3||Cmax fixed-parameter tractable for the maximum processing time pmax? Om||Cmax is fixed-parameter tractable for pmax.

The yes side. Source: open problem 11 of Mnich and van Bevern (2018).
-/
def ZooShops_p126_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p126) (lift (Ops.pmax ZooShops.p126))

/-- `F3||Cmax`, parameter pmax: Is F3||Cmax fixed-parameter tractable for the maximum processing time pmax? Om||Cmax is fixed-parameter tractable for pmax.

The no side. Source: open problem 11 of Mnich and van Bevern (2018).
-/
def ZooShops_p126_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p126) 1 (lift (Ops.pmax ZooShops.p126))

/-- `J3||Cmax`, parameter pmax+nmax: Is J3||Cmax fixed-parameter tractable for the maximum processing time pmax together with the maximum number nmax of operations per job?

The yes side. Source: open problem 12 of Mnich and van Bevern (2018).
-/
def ZooShops_p324_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p324) (tplus (lift (Ops.pmax ZooShops.p324)) (lift (Ops.nmax ZooShops.p324)))

/-- `J3||Cmax`, parameter pmax+nmax: Is J3||Cmax fixed-parameter tractable for the maximum processing time pmax together with the maximum number nmax of operations per job?

The no side. Source: open problem 12 of Mnich and van Bevern (2018).
-/
def ZooShops_p324_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p324) 1 (tplus (lift (Ops.pmax ZooShops.p324)) (lift (Ops.nmax ZooShops.p324)))

/-- `J||Cmax`, parameter m: Is there a (1+ε)-approximation for J||Cmax running in time f(m, ε)·poly(n), a fixed-parameter approximation scheme for the number of machines?

The yes side. Source: open problem 13 of Mnich and van Bevern (2018).
-/
def ZooShops_p325_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  ParamScheme (R.at ZooShops.p325) (Ops.m ZooShops.p325)

/-- `J||Cmax`, parameter m: Is there a (1+ε)-approximation for J||Cmax running in time f(m, ε)·poly(n), a fixed-parameter approximation scheme for the number of machines?

The no side. Source: open problem 13 of Mnich and van Bevern (2018).
-/
def ZooShops_p325_q0_no (R : Reading OperationsFamily.family) : Prop :=
  ¬ Lax496464.WH_B4_Hierarchies.W 1 ⊆ FPT → ¬ ParamScheme (R.at ZooShops.p325) (Ops.m ZooShops.p325)

/-- `O|pij=1;STsd,b|Cmax`, parameter g: Is O|pij=1;STsd,b|Cmax fixed-parameter tractable for the number g of batches? It is polynomial when the number of machines and the number of batches are both constants.

The yes side. Source: open problem 14 of Mnich and van Bevern (2018).
-/
def ZooShops_p326_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p326) (lift (Ops.numBatches ZooShops.p326))

/-- `O|pij=1;STsd,b|Cmax`, parameter g: Is O|pij=1;STsd,b|Cmax fixed-parameter tractable for the number g of batches? It is polynomial when the number of machines and the number of batches are both constants.

The no side. Source: open problem 14 of Mnich and van Bevern (2018).
-/
def ZooShops_p326_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p326) 1 (lift (Ops.numBatches ZooShops.p326))

/-- `O|pij=1;rj|ΣwjUj`, parameter m: Is O|pij=1;rj|ΣwjUj fixed-parameter tractable for the number of machines? The special case with Cmax is polynomial, and the problem is equivalent to P|pj=m;rj|ΣwjUj with preemption at integer times.

The yes side. Source: open problem 15 of Mnich and van Bevern (2018).
-/
def ZooShops_p9_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p9) (lift (Ops.m ZooShops.p9))

/-- `O|pij=1;rj|ΣwjUj`, parameter m: Is O|pij=1;rj|ΣwjUj fixed-parameter tractable for the number of machines? The special case with Cmax is polynomial, and the problem is equivalent to P|pj=m;rj|ΣwjUj with preemption at integer times.

The no side. Source: open problem 15 of Mnich and van Bevern (2018).
-/
def ZooShops_p9_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p9) 1 (lift (Ops.m ZooShops.p9))

/-- `1|chains;s-batch|ΣCj`: Is 1|chains;s-batch|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p2_q0_yes (R : Reading BatchFamily.family) : Prop :=
  PseudoPoly (R.at ZooSerialBatching.p2)

/-- `1|chains;s-batch|ΣCj`: Is 1|chains;s-batch|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p2_q0_no (R : Reading BatchFamily.family) : Prop :=
  StronglyNPHard (R.at ZooSerialBatching.p2)

/-- `F|intree;pij=1|ΣCj`: Is F|intree;pij=1|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p8_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p8)

/-- `F|intree;pij=1|ΣCj`: Is F|intree;pij=1|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p8_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p8)

/-- `P|pj=p;pmtn|ΣwjUj`: Is P|pj=p;pmtn|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p2_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p2)

/-- `P|pj=p;pmtn|ΣwjUj`: Is P|pj=p;pmtn|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p2_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p2)

/-- `F|Mj;prec;rj;n=k|ΣwjUj`: Is F|Mj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p12_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p12)

/-- `F|Mj;prec;rj;n=k|ΣwjUj`: Is F|Mj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p12_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p12)

/-- `F|Mj;prec;rj;n=k|ΣwjTj`: Is F|Mj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p13_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p13)

/-- `F|Mj;prec;rj;n=k|ΣwjTj`: Is F|Mj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p13_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p13)

/-- `O|Mj;prec;rj;n=k|ΣwjUj`: Is O|Mj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p14_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p14)

/-- `O|Mj;prec;rj;n=k|ΣwjUj`: Is O|Mj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p14_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p14)

/-- `O|Mj;prec;rj;n=k|ΣwjTj`: Is O|Mj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p15_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p15)

/-- `O|Mj;prec;rj;n=k|ΣwjTj`: Is O|Mj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p15_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p15)

/-- `P|pj=p;intree|ΣCj`: Is P|pj=p;intree|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p27_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p27)

/-- `P|pj=p;intree|ΣCj`: Is P|pj=p;intree|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p27_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p27)

/-- `P|pj=p;tree|ΣCj`: Is P|pj=p;tree|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p28_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p28)

/-- `P|pj=p;tree|ΣCj`: Is P|pj=p;tree|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p28_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p28)

/-- `P|rj;pj=p|ΣwjUj`: Is P|rj;pj=p|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p29_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p29)

/-- `P|rj;pj=p|ΣwjUj`: Is P|rj;pj=p|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p29_q1_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p29)

/-- `O|pij=1;intree;no-wait|ΣCj`: Is O|pij=1;intree;no-wait|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p21_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p21)

/-- `O|pij=1;intree;no-wait|ΣCj`: Is O|pij=1;intree;no-wait|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p21_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p21)

/-- `O|pij=1;rj;no-wait|ΣwjUj`: Is O|pij=1;rj;no-wait|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p22_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p22)

/-- `O|pij=1;rj;no-wait|ΣwjUj`: Is O|pij=1;rj;no-wait|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p22_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p22)

/-- `P2||ΣwjCj`: Is P2||ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p32_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p32)

/-- `P2||ΣwjCj`: Is P2||ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p32_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p32)

/-- `P2|pmtn|ΣwjCj`: Is P2|pmtn|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p11_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p11)

/-- `P2|pmtn|ΣwjCj`: Is P2|pmtn|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p11_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p11)

/-- `P2|Mj|ΣwjCj`: Is P2|Mj|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p34_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p34)

/-- `P2|Mj|ΣwjCj`: Is P2|Mj|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p34_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p34)

/-- `P2;S1|pj=p|Cmax`: Is P2;S1|pj=p|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p40_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p40)

/-- `P2;S1|pj=p|Cmax`: Is P2;S1|pj=p|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p40_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p40)

/-- `P2;S1|pj=p|ΣCj`: Is P2;S1|pj=p|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p41_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p41)

/-- `P2;S1|pj=p|ΣCj`: Is P2;S1|pj=p|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p41_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p41)

/-- `P|pmtn;rj;sizej|Lmax`: Is P|pmtn;rj;sizej|Lmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p12_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p12)

/-- `P|pmtn;rj;sizej|Lmax`: Is P|pmtn;rj;sizej|Lmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p12_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p12)

/-- `P2|Mj;chains;pj=1|Cmax`: Is P2|Mj;chains;pj=1|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p59_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p59)

/-- `P2|Mj;chains;pj=1|Cmax`: Is P2|Mj;chains;pj=1|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p59_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p59)

/-- `F|Mj;n=3|Cmax`: Is F|Mj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p46_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p46)

/-- `F|Mj;n=3|Cmax`: Is F|Mj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p46_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p46)

/-- `F|Mj;rj;pij=1|Cmax`: Is F|Mj;rj;pij=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p47_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p47)

/-- `F|Mj;rj;pij=1|Cmax`: Is F|Mj;rj;pij=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p47_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p47)

/-- `F|Mj;rj;pij=1|ΣCj`: Is F|Mj;rj;pij=1|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p48_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p48)

/-- `F|Mj;rj;pij=1|ΣCj`: Is F|Mj;rj;pij=1|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p48_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p48)

/-- `F|Mj;pij=1|ΣwjCj`: Is F|Mj;pij=1|ΣwjCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p49_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p49)

/-- `F|Mj;pij=1|ΣwjCj`: Is F|Mj;pij=1|ΣwjCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p49_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p49)

/-- `F|Mj;pij=1|ΣwjUj`: Is F|Mj;pij=1|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p50_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p50)

/-- `F|Mj;pij=1|ΣwjUj`: Is F|Mj;pij=1|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p50_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p50)

/-- `F|Mj;pij=1|ΣTj`: Is F|Mj;pij=1|ΣTj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p51_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p51)

/-- `F|Mj;pij=1|ΣTj`: Is F|Mj;pij=1|ΣTj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p51_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p51)

/-- `O|Mj;rj;pij=1|Cmax`: Is O|Mj;rj;pij=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p54_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p54)

/-- `O|Mj;rj;pij=1|Cmax`: Is O|Mj;rj;pij=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p54_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p54)

/-- `O|Mj;rj;pij=1|ΣCj`: Is O|Mj;rj;pij=1|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p55_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p55)

/-- `O|Mj;rj;pij=1|ΣCj`: Is O|Mj;rj;pij=1|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p55_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p55)

/-- `O|Mj;pij=1|ΣwjCj`: Is O|Mj;pij=1|ΣwjCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p56_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p56)

/-- `O|Mj;pij=1|ΣwjCj`: Is O|Mj;pij=1|ΣwjCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p56_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p56)

/-- `O|Mj;pij=1|ΣwjUj`: Is O|Mj;pij=1|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p57_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p57)

/-- `O|Mj;pij=1|ΣwjUj`: Is O|Mj;pij=1|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p57_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p57)

/-- `O|Mj;pij=1|ΣTj`: Is O|Mj;pij=1|ΣTj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p58_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p58)

/-- `O|Mj;pij=1|ΣTj`: Is O|Mj;pij=1|ΣTj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p58_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p58)

/-- `F|fixj;rj;pij=1|Cmax`: Is F|fixj;rj;pij=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p69_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p69)

/-- `F|fixj;rj;pij=1|Cmax`: Is F|fixj;rj;pij=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p69_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p69)

/-- `F|fixj;rj;pij=1|ΣCj`: Is F|fixj;rj;pij=1|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p70_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p70)

/-- `F|fixj;rj;pij=1|ΣCj`: Is F|fixj;rj;pij=1|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p70_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p70)

/-- `F|fixj;pij=1|ΣwjCj`: Is F|fixj;pij=1|ΣwjCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p71_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p71)

/-- `F|fixj;pij=1|ΣwjCj`: Is F|fixj;pij=1|ΣwjCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p71_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p71)

/-- `F|fixj;pij=1|ΣwjUj`: Is F|fixj;pij=1|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p72_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p72)

/-- `F|fixj;pij=1|ΣwjUj`: Is F|fixj;pij=1|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p72_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p72)

/-- `F|fixj;pij=1|ΣwjTj`: Is F|fixj;pij=1|ΣwjTj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p73_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p73)

/-- `F|fixj;pij=1|ΣwjTj`: Is F|fixj;pij=1|ΣwjTj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p73_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p73)

/-- `O|fixj;rj;pij=1|Cmax`: Is O|fixj;rj;pij=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p76_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p76)

/-- `O|fixj;rj;pij=1|Cmax`: Is O|fixj;rj;pij=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p76_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p76)

/-- `O|fixj;rj;pij=1|ΣCj`: Is O|fixj;rj;pij=1|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p77_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p77)

/-- `O|fixj;rj;pij=1|ΣCj`: Is O|fixj;rj;pij=1|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p77_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p77)

/-- `O|fixj;pij=1|ΣwjCj`: Is O|fixj;pij=1|ΣwjCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p78_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p78)

/-- `O|fixj;pij=1|ΣwjCj`: Is O|fixj;pij=1|ΣwjCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p78_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p78)

/-- `O|fixj;pij=1|ΣwjUj`: Is O|fixj;pij=1|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p79_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p79)

/-- `O|fixj;pij=1|ΣwjUj`: Is O|fixj;pij=1|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p79_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p79)

/-- `O|fixj;pij=1|ΣTj`: Is O|fixj;pij=1|ΣTj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p80_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p80)

/-- `O|fixj;pij=1|ΣTj`: Is O|fixj;pij=1|ΣTj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p80_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p80)

/-- `J|n=k;pmtn|Cmax`: Is J|n=k;pmtn|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p0_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooPreemptiveShops.p0)

/-- `J|n=k;pmtn|Cmax`: Is J|n=k;pmtn|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p0_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooPreemptiveShops.p0)

/-- `J|n=k;pmtn|ΣCj`: Is J|n=k;pmtn|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p1_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooPreemptiveShops.p1)

/-- `J|n=k;pmtn|ΣCj`: Is J|n=k;pmtn|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p1_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooPreemptiveShops.p1)

/-- `J2|n=3;pmtn|Cmax`: Is J2|n=3;pmtn|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p2_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptiveShops.p2)

/-- `J2|n=3;pmtn|Cmax`: Is J2|n=3;pmtn|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p2_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptiveShops.p2)

/-- `J2|n=3;pmtn|ΣCj`: Is J2|n=3;pmtn|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p3_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptiveShops.p3)

/-- `J2|n=3;pmtn|ΣCj`: Is J2|n=3;pmtn|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p3_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptiveShops.p3)

/-- `F2;S1|pij=p|Cmax`: Is F2;S1|pij=p|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p99_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p99)

/-- `F2;S1|pij=p|Cmax`: Is F2;S1|pij=p|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p99_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p99)

/-- `F2;S1|pij=1|ΣwjUj`: Is F2;S1|pij=1|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p105_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p105)

/-- `F2;S1|pij=1|ΣwjUj`: Is F2;S1|pij=1|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p105_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p105)

/-- `F3;S1|pij=1|ΣwjUj`: Is F3;S1|pij=1|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p106_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p106)

/-- `F3;S1|pij=1|ΣwjUj`: Is F3;S1|pij=1|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p106_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p106)

/-- `F2;S1|pij=1|ΣTj`: Is F2;S1|pij=1|ΣTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p107_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p107)

/-- `F2;S1|pij=1|ΣTj`: Is F2;S1|pij=1|ΣTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p107_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p107)

/-- `F3;S1|pij=1|ΣTj`: Is F3;S1|pij=1|ΣTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p108_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p108)

/-- `F3;S1|pij=1|ΣTj`: Is F3;S1|pij=1|ΣTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p108_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p108)

/-- `P|pmtn;pj=1;sizej|Cmax`: Is P|pmtn;pj=1;sizej|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p22_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p22)

/-- `P|pmtn;pj=1;sizej|Cmax`: Is P|pmtn;pj=1;sizej|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p22_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p22)

/-- `P|pmtn;sizej|ΣCj`: Is P|pmtn;sizej|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p23_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p23)

/-- `P|pmtn;sizej|ΣCj`: Is P|pmtn;sizej|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p23_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p23)

/-- `O2|pmtn|ΣCj`: Is O2|pmtn|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p9_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptiveShops.p9)

/-- `O2|pmtn|ΣCj`: Is O2|pmtn|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p9_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptiveShops.p9)

/-- `Q|pj=1;rj|ΣCj`: Is Q|pj=1;rj|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p98_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p98)

/-- `Q|pj=1;rj|ΣCj`: Is Q|pj=1;rj|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p98_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p98)

/-- `Q|pj=p;rj|ΣCj`: Is Q|pj=p;rj|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p99_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p99)

/-- `Q|pj=p;rj|ΣCj`: Is Q|pj=p;rj|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p99_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p99)

/-- `P2|pmtn;rj|ΣUj`: Is P2|pmtn;rj|ΣUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p25_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p25)

/-- `P2|pmtn;rj|ΣUj`: Is P2|pmtn;rj|ΣUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p25_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p25)

/-- `P2|pmtn;rj|ΣCj`: Is P2|pmtn;rj|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p26_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p26)

/-- `P2|pmtn;rj|ΣCj`: Is P2|pmtn;rj|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p26_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p26)

/-- `O3||Cmax`: Is O3||Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p133_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p133)

/-- `O3||Cmax`: Is O3||Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p133_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p133)

/-- `O|fixj;n=3|Cmax`: Is O|fixj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p134_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p134)

/-- `O|fixj;n=3|Cmax`: Is O|fixj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p134_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p134)

/-- `O3|fixj|Cmax`: Is O3|fixj|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p135_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p135)

/-- `O3|fixj|Cmax`: Is O3|fixj|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p135_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p135)

/-- `O|Mj;n=3|Cmax`: Is O|Mj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p136_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p136)

/-- `O|Mj;n=3|Cmax`: Is O|Mj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p136_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p136)

/-- `O3|Mj|Cmax`: Is O3|Mj|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p137_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p137)

/-- `O3|Mj|Cmax`: Is O3|Mj|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p137_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p137)

/-- `P2;S1|sj=1|Cmax`: Is P2;S1|sj=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p112_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p112)

/-- `P2;S1|sj=1|Cmax`: Is P2;S1|sj=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p112_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p112)

/-- `O|Mj;pij=1|Cmax`: Is O|Mj;pij=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p148_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p148)

/-- `O|Mj;pij=1|Cmax`: Is O|Mj;pij=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p148_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p148)

/-- `F|fixj;prec;rj;n=k|ΣwjUj`: Is F|fixj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p150_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p150)

/-- `F|fixj;prec;rj;n=k|ΣwjUj`: Is F|fixj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p150_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p150)

/-- `F|fixj;prec;rj;n=k|ΣwjTj`: Is F|fixj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p151_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p151)

/-- `F|fixj;prec;rj;n=k|ΣwjTj`: Is F|fixj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p151_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p151)

/-- `O|fixj;prec;rj;n=k|ΣwjUj`: Is O|fixj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p153_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p153)

/-- `O|fixj;prec;rj;n=k|ΣwjUj`: Is O|fixj;prec;rj;n=k|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p153_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p153)

/-- `O|fixj;prec;rj;n=k|ΣwjTj`: Is O|fixj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p155_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p155)

/-- `O|fixj;prec;rj;n=k|ΣwjTj`: Is O|fixj;prec;rj;n=k|ΣwjTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p155_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p155)

/-- `F|fixj;n=3|Cmax`: Is F|fixj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p156_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p156)

/-- `F|fixj;n=3|Cmax`: Is F|fixj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p156_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p156)

/-- `F2;R1|pij=1;tj|ΣwjUj`: Is F2;R1|pij=1;tj|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p167_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p167)

/-- `F2;R1|pij=1;tj|ΣwjUj`: Is F2;R1|pij=1;tj|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p167_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p167)

/-- `F3;R1|pij=1;tjk|ΣwjUj`: Is F3;R1|pij=1;tjk|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p168_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p168)

/-- `F3;R1|pij=1;tjk|ΣwjUj`: Is F3;R1|pij=1;tjk|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p168_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p168)

/-- `F2;R1|pij=1;tj|ΣTj`: Is F2;R1|pij=1;tj|ΣTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p169_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p169)

/-- `F2;R1|pij=1;tj|ΣTj`: Is F2;R1|pij=1;tj|ΣTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p169_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p169)

/-- `F3;R1|pij=1;tjk|ΣTj`: Is F3;R1|pij=1;tjk|ΣTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p170_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p170)

/-- `F3;R1|pij=1;tjk|ΣTj`: Is F3;R1|pij=1;tjk|ΣTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p170_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p170)

/-- `J2|Mj;pij=1|ΣwjUj`: Is J2|Mj;pij=1|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p175_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p175)

/-- `J2|Mj;pij=1|ΣwjUj`: Is J2|Mj;pij=1|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p175_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p175)

/-- `Q|pmtn|ΣUj`: Is Q|pmtn|ΣUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p40_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p40)

/-- `Q|pmtn|ΣUj`: Is Q|pmtn|ΣUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p40_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p40)

/-- `Q|pmtn|ΣwjUj`: Is Q|pmtn|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p41_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p41)

/-- `Q|pmtn|ΣwjUj`: Is Q|pmtn|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p41_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p41)

/-- `P|pmtn|ΣUj`: Is P|pmtn|ΣUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p45_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p45)

/-- `P|pmtn|ΣUj`: Is P|pmtn|ΣUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p45_q1_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p45)

/-- `1|rj;pmtn|ΣwjUj`: Is 1|rj;pmtn|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p47_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooPreemptive.p47)

/-- `1|rj;pmtn|ΣwjUj`: Is 1|rj;pmtn|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p47_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooPreemptive.p47)

/-- `P2|sizej|ΣCj`: Is P2|sizej|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p143_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p143)

/-- `P2|sizej|ΣCj`: Is P2|sizej|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p143_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p143)

/-- `O2|pmtn|ΣUj`: Is O2|pmtn|ΣUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p17_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptiveShops.p17)

/-- `O2|pmtn|ΣUj`: Is O2|pmtn|ΣUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p17_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptiveShops.p17)

/-- `P2|Mj|Cmax`: Is P2|Mj|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p161_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p161)

/-- `P2|Mj|Cmax`: Is P2|Mj|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p161_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p161)

/-- `F2|Mj|Cmax`: Is F2|Mj|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p208_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p208)

/-- `F2|Mj|Cmax`: Is F2|Mj|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p208_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p208)

/-- `J|prec;rj;n=k|ΣwjUj`: Is J|prec;rj;n=k|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p214_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p214)

/-- `J|prec;rj;n=k|ΣwjUj`: Is J|prec;rj;n=k|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p214_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p214)

/-- `J|prec;rj;n=k|ΣwjTj`: Is J|prec;rj;n=k|ΣwjTj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p215_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p215)

/-- `J|prec;rj;n=k|ΣwjTj`: Is J|prec;rj;n=k|ΣwjTj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p215_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p215)

/-- `J|prec;rj;n=k;pmtn|ΣwjUj`: Is J|prec;rj;n=k;pmtn|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p19_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooPreemptiveShops.p19)

/-- `J|prec;rj;n=k;pmtn|ΣwjUj`: Is J|prec;rj;n=k;pmtn|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p19_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooPreemptiveShops.p19)

/-- `J|prec;rj;n=k;pmtn|ΣwjTj`: Is J|prec;rj;n=k;pmtn|ΣwjTj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p20_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooPreemptiveShops.p20)

/-- `J|prec;rj;n=k;pmtn|ΣwjTj`: Is J|prec;rj;n=k;pmtn|ΣwjTj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptiveShops_p20_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooPreemptiveShops.p20)

/-- `J3|n=3|Cmax`: Is J3|n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p229_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p229)

/-- `J3|n=3|Cmax`: Is J3|n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p229_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p229)

/-- `J3|n=3|ΣCj`: Is J3|n=3|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p230_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p230)

/-- `J3|n=3|ΣCj`: Is J3|n=3|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p230_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p230)

/-- `J3|fixj;n=3|Cmax`: Is J3|fixj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p231_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p231)

/-- `J3|fixj;n=3|Cmax`: Is J3|fixj;n=3|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p231_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p231)

/-- `J3|fixj;n=3|ΣCj`: Is J3|fixj;n=3|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p232_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p232)

/-- `J3|fixj;n=3|ΣCj`: Is J3|fixj;n=3|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p232_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p232)

/-- `J3|Mj;n=3|ΣCj`: Is J3|Mj;n=3|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p233_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p233)

/-- `J3|Mj;n=3|ΣCj`: Is J3|Mj;n=3|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p233_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p233)

/-- `J2|pij=1;rj|ΣUj`: Is J2|pij=1;rj|ΣUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p237_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p237)

/-- `J2|pij=1;rj|ΣUj`: Is J2|pij=1;rj|ΣUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p237_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p237)

/-- `J2|pij=1;rj|ΣCj`: Is J2|pij=1;rj|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p238_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p238)

/-- `J2|pij=1;rj|ΣCj`: Is J2|pij=1;rj|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p238_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p238)

/-- `J2|pij=1|ΣwjCj`: Is J2|pij=1|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p240_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p240)

/-- `J2|pij=1|ΣwjCj`: Is J2|pij=1|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p240_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p240)

/-- `J2|pij=1;no-wait|ΣwjCj`: Is J2|pij=1;no-wait|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p247_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p247)

/-- `J2|pij=1;no-wait|ΣwjCj`: Is J2|pij=1;no-wait|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p247_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p247)

/-- `J2|fixj;rj;pij=1|ΣCj`: Is J2|fixj;rj;pij=1|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p249_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p249)

/-- `J2|fixj;rj;pij=1|ΣCj`: Is J2|fixj;rj;pij=1|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p249_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p249)

/-- `J2|fixj;pij=1|ΣwjCj`: Is J2|fixj;pij=1|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p251_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p251)

/-- `J2|fixj;pij=1|ΣwjCj`: Is J2|fixj;pij=1|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p251_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p251)

/-- `J2|Mj;rj;pij=1|ΣCj`: Is J2|Mj;rj;pij=1|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p253_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p253)

/-- `J2|Mj;rj;pij=1|ΣCj`: Is J2|Mj;rj;pij=1|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p253_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p253)

/-- `J2|Mj;pij=1|ΣwjCj`: Is J2|Mj;pij=1|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p255_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p255)

/-- `J2|Mj;pij=1|ΣwjCj`: Is J2|Mj;pij=1|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p255_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p255)

/-- `J2|Mj;rj;pij=1|ΣUj`: Is J2|Mj;rj;pij=1|ΣUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p257_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p257)

/-- `J2|Mj;rj;pij=1|ΣUj`: Is J2|Mj;rj;pij=1|ΣUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p257_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p257)

/-- `O|pij=1;outtree|Lmax`: Is O|pij=1;outtree|Lmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p261_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p261)

/-- `O|pij=1;outtree|Lmax`: Is O|pij=1;outtree|Lmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p261_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p261)

/-- `O|pij=1;rj;no-wait|ΣwjCj`: Is O|pij=1;rj;no-wait|ΣwjCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p272_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p272)

/-- `O|pij=1;rj;no-wait|ΣwjCj`: Is O|pij=1;rj;no-wait|ΣwjCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p272_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p272)

/-- `O|pij=1;rj;no-wait|ΣTj`: Is O|pij=1;rj;no-wait|ΣTj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p273_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooShops.p273)

/-- `O|pij=1;rj;no-wait|ΣTj`: Is O|pij=1;rj;no-wait|ΣTj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p273_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooShops.p273)

/-- `O2|tjkl=T|Cmax`: Is O2|tjkl=T|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p305_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p305)

/-- `O2|tjkl=T|Cmax`: Is O2|tjkl=T|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p305_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p305)

/-- `P2|pmtn|ΣwjUj`: Is P2|pmtn|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p60_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p60)

/-- `P2|pmtn|ΣwjUj`: Is P2|pmtn|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p60_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p60)

/-- `1|interval order|ΣwjCj`: Is 1|interval order|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p210_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p210)

/-- `1|interval order|ΣwjCj`: Is 1|interval order|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p210_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p210)

/-- `P|opposing forest;pj=p|Cmax`: Is P|opposing forest;pj=p|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p211_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p211)

/-- `P|opposing forest;pj=p|Cmax`: Is P|opposing forest;pj=p|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p211_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p211)

/-- `P|opposing forest;pj=1|Cmax`: Is P|opposing forest;pj=1|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p212_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p212)

/-- `P|opposing forest;pj=1|Cmax`: Is P|opposing forest;pj=1|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p212_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p212)

/-- `P|level order;pj=p|Cmax`: Is P|level order;pj=p|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p214_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p214)

/-- `P|level order;pj=p|Cmax`: Is P|level order;pj=p|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p214_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p214)

/-- `P|prec;l=1;pj=1|Cmax`: Is P|prec;l=1;pj=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p220_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p220)

/-- `P|prec;l=1;pj=1|Cmax`: Is P|prec;l=1;pj=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p220_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p220)

/-- `R|rj|ΣCj`: Is R|rj|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p221_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p221)

/-- `R|rj|ΣCj`: Is R|rj|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p221_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p221)

/-- `P|prec;l=1;pj=1|ΣCj`: Is P|prec;l=1;pj=1|ΣCj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p224_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p224)

/-- `P|prec;l=1;pj=1|ΣCj`: Is P|prec;l=1;pj=1|ΣCj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p224_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p224)

/-- `1|pj=1;prec;lij≤0|Lmax`: Is 1|pj=1;prec;lij≤0|Lmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p228_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p228)

/-- `1|pj=1;prec;lij≤0|Lmax`: Is 1|pj=1;prec;lij≤0|Lmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p228_q0_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p228)

/-- `P|rj;pj=p|ΣUj`: Is P|rj;pj=p|ΣUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p238_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallel.p238)

/-- `P|rj;pj=p|ΣUj`: Is P|rj;pj=p|ΣUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p238_q1_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallel.p238)

/-- `1|s-batch(∞);rj|ΣwjUj`: Is 1|s-batch(∞);rj|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p19_q0_yes (R : Reading BatchFamily.family) : Prop :=
  PseudoPoly (R.at ZooSerialBatching.p19)

/-- `1|s-batch(∞);rj|ΣwjUj`: Is 1|s-batch(∞);rj|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p19_q0_no (R : Reading BatchFamily.family) : Prop :=
  StronglyNPHard (R.at ZooSerialBatching.p19)

/-- `1|s-batch(∞)|ΣwjUj`: Is 1|s-batch(∞)|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p20_q0_yes (R : Reading BatchFamily.family) : Prop :=
  InP (R.at ZooSerialBatching.p20)

/-- `1|s-batch(∞)|ΣwjUj`: Is 1|s-batch(∞)|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p20_q0_no (R : Reading BatchFamily.family) : Prop :=
  NPHard (R.at ZooSerialBatching.p20)

/-- `1|s-batch(b)|ΣwjUj`: Is 1|s-batch(b)|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p21_q0_yes (R : Reading BatchFamily.family) : Prop :=
  InP (R.at ZooSerialBatching.p21)

/-- `1|s-batch(b)|ΣwjUj`: Is 1|s-batch(b)|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p21_q0_no (R : Reading BatchFamily.family) : Prop :=
  NPHard (R.at ZooSerialBatching.p21)

/-- `1|s-batch(b);rj|ΣwjUj`: Is 1|s-batch(b);rj|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p22_q0_yes (R : Reading BatchFamily.family) : Prop :=
  PseudoPoly (R.at ZooSerialBatching.p22)

/-- `1|s-batch(b);rj|ΣwjUj`: Is 1|s-batch(b);rj|ΣwjUj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooSerialBatching_p22_q0_no (R : Reading BatchFamily.family) : Prop :=
  StronglyNPHard (R.at ZooSerialBatching.p22)

/-- `1|p-batch;sizej|ΣCj`: Is 1|p-batch;sizej|ΣCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallelBatching_p32_q0_yes (R : Reading BatchFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallelBatching.p32)

/-- `1|p-batch;sizej|ΣCj`: Is 1|p-batch;sizej|ΣCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallelBatching_p32_q0_no (R : Reading BatchFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallelBatching.p32)

/-- `1|p-batch;sizej|ΣwjCj`: Is 1|p-batch;sizej|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallelBatching_p33_q0_yes (R : Reading BatchFamily.family) : Prop :=
  PseudoPoly (R.at ZooParallelBatching.p33)

/-- `1|p-batch;sizej|ΣwjCj`: Is 1|p-batch;sizej|ΣwjCj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallelBatching_p33_q0_no (R : Reading BatchFamily.family) : Prop :=
  StronglyNPHard (R.at ZooParallelBatching.p33)

/-- `1|p-batch;sizej|Cmax`: Is 1|p-batch;sizej|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallelBatching_p34_q0_yes (R : Reading BatchFamily.family) : Prop :=
  InP (R.at ZooParallelBatching.p34)

/-- `1|p-batch;sizej|Cmax`: Is 1|p-batch;sizej|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallelBatching_p34_q0_no (R : Reading BatchFamily.family) : Prop :=
  NPHard (R.at ZooParallelBatching.p34)

/-- `P∞|pj=1;prec;c=1|Cmax`: Is P∞|pj=1;prec;c=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p244_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p244)

/-- `P∞|pj=1;prec;c=1|Cmax`: Is P∞|pj=1;prec;c=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p244_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p244)

/-- `P∞|pj=1;prec;c|Cmax`: Is P∞|pj=1;prec;c|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p246_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p246)

/-- `P∞|pj=1;prec;c|Cmax`: Is P∞|pj=1;prec;c|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p246_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p246)

/-- `P∞|prec;c|Cmax`: Is P∞|prec;c|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p249_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p249)

/-- `P∞|prec;c|Cmax`: Is P∞|prec;c|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p249_q0_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p249)

/-- `1|forbidden-times|Cmax`: Is 1|forbidden-times|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p253_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p253)

/-- `1|forbidden-times|Cmax`: Is 1|forbidden-times|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p253_q1_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p253)

/-- `P3|prec;pj=1|Cmax`: Is P3|prec;pj=1|Cmax in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p255_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooParallel.p255)

/-- `P3|prec;pj=1|Cmax`: Is P3|prec;pj=1|Cmax in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooParallel_p255_q1_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooParallel.p255)

/-- `P|pmtn|ΣTj`: Is P|pmtn|ΣTj pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p74_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooPreemptive.p74)

/-- `P|pmtn|ΣTj`: Is P|pmtn|ΣTj pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p74_q1_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooPreemptive.p74)

/-- `P2|pmtn;pj=p|ΣwjUj`: Is P2|pmtn;pj=p|ΣwjUj in P, or NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p75_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  InP (R.at ZooPreemptive.p75)

/-- `P2|pmtn;pj=p|ΣwjUj`: Is P2|pmtn;pj=p|ΣwjUj in P, or NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooPreemptive_p75_q1_no (R : Reading OperationsFamily.family) : Prop :=
  NPHard (R.at ZooPreemptive.p75)

/-- `O|pij=1;STsd,b|Cmax`: Is O|pij=1;STsd,b|Cmax pseudo-polynomial, or strongly NP-hard?

The yes side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p326_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  PseudoPoly (R.at ZooShops.p326)

/-- `O|pij=1;STsd,b|Cmax`: Is O|pij=1;STsd,b|Cmax pseudo-polynomial, or strongly NP-hard?

The no side. Source: the zoo's data, carried along its arrows.
-/
def ZooShops_p326_q1_no (R : Reading OperationsFamily.family) : Prop :=
  StronglyNPHard (R.at ZooShops.p326)

/-- `P||ΣUj`, parameter m: Is P||ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p3_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p3) (lift (Ops.m ZooParallel.p3))

/-- `P||ΣUj`, parameter m: Is P||ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p3_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p3) 1 (lift (Ops.m ZooParallel.p3))

/-- `P||ΣwjUj`, parameter m: Is P||ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p4_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p4) (lift (Ops.m ZooParallel.p4))

/-- `P||ΣwjUj`, parameter m: Is P||ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p4_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p4) 1 (lift (Ops.m ZooParallel.p4))

/-- `F|intree;pij=1|ΣCj`, parameter m: Is F|intree;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p8_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p8) (lift (Ops.m ZooShops.p8))

/-- `F|intree;pij=1|ΣCj`, parameter m: Is F|intree;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p8_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p8) 1 (lift (Ops.m ZooShops.p8))

/-- `P|pj=p;rj|ΣwjCj`, parameter m: Is P|pj=p;rj|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p22_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p22) (lift (Ops.m ZooParallel.p22))

/-- `P|pj=p;rj|ΣwjCj`, parameter m: Is P|pj=p;rj|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p22_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p22) 1 (lift (Ops.m ZooParallel.p22))

/-- `P|pj=p;rj|ΣTj`, parameter m: Is P|pj=p;rj|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p23_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p23) (lift (Ops.m ZooParallel.p23))

/-- `P|pj=p;rj|ΣTj`, parameter m: Is P|pj=p;rj|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p23_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p23) 1 (lift (Ops.m ZooParallel.p23))

/-- `P|pj=p;pmtn|ΣwjUj`, parameter m: Is P|pj=p;pmtn|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p2_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p2) (lift (Ops.m ZooPreemptive.p2))

/-- `P|pj=p;pmtn|ΣwjUj`, parameter m: Is P|pj=p;pmtn|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p2_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p2) 1 (lift (Ops.m ZooPreemptive.p2))

/-- `P|rj;pj=p;sizej|Cmax`, parameter m: Is P|rj;pj=p;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p24_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p24) (lift (Ops.m ZooParallel.p24))

/-- `P|rj;pj=p;sizej|Cmax`, parameter m: Is P|rj;pj=p;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p24_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p24) 1 (lift (Ops.m ZooParallel.p24))

/-- `P|rj;pj=p;sizej|ΣCj`, parameter m: Is P|rj;pj=p;sizej|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p25_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p25) (lift (Ops.m ZooParallel.p25))

/-- `P|rj;pj=p;sizej|ΣCj`, parameter m: Is P|rj;pj=p;sizej|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p25_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p25) 1 (lift (Ops.m ZooParallel.p25))

/-- `F|Mj;prec;rj;n=k|ΣwjUj`, parameter m: Is F|Mj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p12_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p12) (lift (Ops.m ZooShops.p12))

/-- `F|Mj;prec;rj;n=k|ΣwjUj`, parameter m: Is F|Mj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p12_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p12) 1 (lift (Ops.m ZooShops.p12))

/-- `F|Mj;prec;rj;n=k|ΣwjTj`, parameter m: Is F|Mj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p13_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p13) (lift (Ops.m ZooShops.p13))

/-- `F|Mj;prec;rj;n=k|ΣwjTj`, parameter m: Is F|Mj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p13_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p13) 1 (lift (Ops.m ZooShops.p13))

/-- `O|Mj;prec;rj;n=k|ΣwjUj`, parameter m: Is O|Mj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p14_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p14) (lift (Ops.m ZooShops.p14))

/-- `O|Mj;prec;rj;n=k|ΣwjUj`, parameter m: Is O|Mj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p14_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p14) 1 (lift (Ops.m ZooShops.p14))

/-- `O|Mj;prec;rj;n=k|ΣwjTj`, parameter m: Is O|Mj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p15_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p15) (lift (Ops.m ZooShops.p15))

/-- `O|Mj;prec;rj;n=k|ΣwjTj`, parameter m: Is O|Mj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p15_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p15) 1 (lift (Ops.m ZooShops.p15))

/-- `P|pj=p;intree|ΣCj`, parameter m: Is P|pj=p;intree|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p27_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p27) (lift (Ops.m ZooParallel.p27))

/-- `P|pj=p;intree|ΣCj`, parameter m: Is P|pj=p;intree|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p27_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p27) 1 (lift (Ops.m ZooParallel.p27))

/-- `P|pj=p;tree|ΣCj`, parameter m: Is P|pj=p;tree|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p28_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p28) (lift (Ops.m ZooParallel.p28))

/-- `P|pj=p;tree|ΣCj`, parameter m: Is P|pj=p;tree|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p28_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p28) 1 (lift (Ops.m ZooParallel.p28))

/-- `P|rj;pj=p|ΣwjUj`, parameter pmax: Is P|rj;pj=p|ΣwjUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p29_q2_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p29) (lift (Ops.pmax ZooParallel.p29))

/-- `P|rj;pj=p|ΣwjUj`, parameter pmax: Is P|rj;pj=p|ΣwjUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p29_q2_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p29) 1 (lift (Ops.pmax ZooParallel.p29))

/-- `P|pj=p;pmtn|ΣCj`, parameter m: Is P|pj=p;pmtn|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p7_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p7) (lift (Ops.m ZooPreemptive.p7))

/-- `P|pj=p;pmtn|ΣCj`, parameter m: Is P|pj=p;pmtn|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p7_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p7) 1 (lift (Ops.m ZooPreemptive.p7))

/-- `Q|pj=p;pmtn|ΣUj`, parameter m: Is Q|pj=p;pmtn|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p8_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p8) (lift (Ops.m ZooPreemptive.p8))

/-- `Q|pj=p;pmtn|ΣUj`, parameter m: Is Q|pj=p;pmtn|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p8_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p8) 1 (lift (Ops.m ZooPreemptive.p8))

/-- `O|pij=1;intree;no-wait|ΣCj`, parameter m: Is O|pij=1;intree;no-wait|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p21_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p21) (lift (Ops.m ZooShops.p21))

/-- `O|pij=1;intree;no-wait|ΣCj`, parameter m: Is O|pij=1;intree;no-wait|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p21_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p21) 1 (lift (Ops.m ZooShops.p21))

/-- `O|pij=1;rj;no-wait|ΣwjUj`, parameter m: Is O|pij=1;rj;no-wait|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p22_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p22) (lift (Ops.m ZooShops.p22))

/-- `O|pij=1;rj;no-wait|ΣwjUj`, parameter m: Is O|pij=1;rj;no-wait|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p22_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p22) 1 (lift (Ops.m ZooShops.p22))

/-- `P|fixj;rj;pmtn|Lmax`, parameter m: Is P|fixj;rj;pmtn|Lmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p10_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p10) (lift (Ops.m ZooPreemptive.p10))

/-- `P|fixj;rj;pmtn|Lmax`, parameter m: Is P|fixj;rj;pmtn|Lmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p10_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p10) 1 (lift (Ops.m ZooPreemptive.p10))

/-- `P|pj=p;sizej|Cmax`, parameter m: Is P|pj=p;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p46_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p46) (lift (Ops.m ZooParallel.p46))

/-- `P|pj=p;sizej|Cmax`, parameter m: Is P|pj=p;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p46_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p46) 1 (lift (Ops.m ZooParallel.p46))

/-- `P|pmtn;rj;sizej|Lmax`, parameter m: Is P|pmtn;rj;sizej|Lmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p12_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p12) (lift (Ops.m ZooPreemptive.p12))

/-- `P|pmtn;rj;sizej|Lmax`, parameter m: Is P|pmtn;rj;sizej|Lmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p12_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p12) 1 (lift (Ops.m ZooPreemptive.p12))

/-- `O|pij=1|ΣwjCj`, parameter m: Is O|pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p39_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p39) (lift (Ops.m ZooShops.p39))

/-- `O|pij=1|ΣwjCj`, parameter m: Is O|pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p39_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p39) 1 (lift (Ops.m ZooShops.p39))

/-- `F|Mj;rj;pij=1|Cmax`, parameter m: Is F|Mj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p47_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p47) (lift (Ops.m ZooShops.p47))

/-- `F|Mj;rj;pij=1|Cmax`, parameter m: Is F|Mj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p47_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p47) 1 (lift (Ops.m ZooShops.p47))

/-- `F|Mj;rj;pij=1|ΣCj`, parameter m: Is F|Mj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p48_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p48) (lift (Ops.m ZooShops.p48))

/-- `F|Mj;rj;pij=1|ΣCj`, parameter m: Is F|Mj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p48_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p48) 1 (lift (Ops.m ZooShops.p48))

/-- `F|Mj;pij=1|ΣwjCj`, parameter m: Is F|Mj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p49_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p49) (lift (Ops.m ZooShops.p49))

/-- `F|Mj;pij=1|ΣwjCj`, parameter m: Is F|Mj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p49_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p49) 1 (lift (Ops.m ZooShops.p49))

/-- `F|Mj;pij=1|ΣwjUj`, parameter m: Is F|Mj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p50_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p50) (lift (Ops.m ZooShops.p50))

/-- `F|Mj;pij=1|ΣwjUj`, parameter m: Is F|Mj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p50_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p50) 1 (lift (Ops.m ZooShops.p50))

/-- `F|Mj;pij=1|ΣTj`, parameter m: Is F|Mj;pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p51_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p51) (lift (Ops.m ZooShops.p51))

/-- `F|Mj;pij=1|ΣTj`, parameter m: Is F|Mj;pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p51_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p51) 1 (lift (Ops.m ZooShops.p51))

/-- `O|Mj;rj;pij=1|Cmax`, parameter m: Is O|Mj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p54_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p54) (lift (Ops.m ZooShops.p54))

/-- `O|Mj;rj;pij=1|Cmax`, parameter m: Is O|Mj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p54_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p54) 1 (lift (Ops.m ZooShops.p54))

/-- `O|Mj;rj;pij=1|ΣCj`, parameter m: Is O|Mj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p55_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p55) (lift (Ops.m ZooShops.p55))

/-- `O|Mj;rj;pij=1|ΣCj`, parameter m: Is O|Mj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p55_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p55) 1 (lift (Ops.m ZooShops.p55))

/-- `O|Mj;pij=1|ΣwjCj`, parameter m: Is O|Mj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p56_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p56) (lift (Ops.m ZooShops.p56))

/-- `O|Mj;pij=1|ΣwjCj`, parameter m: Is O|Mj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p56_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p56) 1 (lift (Ops.m ZooShops.p56))

/-- `O|Mj;pij=1|ΣwjUj`, parameter m: Is O|Mj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p57_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p57) (lift (Ops.m ZooShops.p57))

/-- `O|Mj;pij=1|ΣwjUj`, parameter m: Is O|Mj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p57_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p57) 1 (lift (Ops.m ZooShops.p57))

/-- `O|Mj;pij=1|ΣTj`, parameter m: Is O|Mj;pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p58_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p58) (lift (Ops.m ZooShops.p58))

/-- `O|Mj;pij=1|ΣTj`, parameter m: Is O|Mj;pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p58_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p58) 1 (lift (Ops.m ZooShops.p58))

/-- `P|fixj;rj;pj=1|Cmax`, parameter m: Is P|fixj;rj;pj=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p64_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p64) (lift (Ops.m ZooParallel.p64))

/-- `P|fixj;rj;pj=1|Cmax`, parameter m: Is P|fixj;rj;pj=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p64_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p64) 1 (lift (Ops.m ZooParallel.p64))

/-- `P|fixj;rj;pj=1|ΣCj`, parameter m: Is P|fixj;rj;pj=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p65_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p65) (lift (Ops.m ZooParallel.p65))

/-- `P|fixj;rj;pj=1|ΣCj`, parameter m: Is P|fixj;rj;pj=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p65_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p65) 1 (lift (Ops.m ZooParallel.p65))

/-- `P|fixj;pj=1|ΣwjCj`, parameter m: Is P|fixj;pj=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p66_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p66) (lift (Ops.m ZooParallel.p66))

/-- `P|fixj;pj=1|ΣwjCj`, parameter m: Is P|fixj;pj=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p66_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p66) 1 (lift (Ops.m ZooParallel.p66))

/-- `P|fixj;pj=1|ΣwjUj`, parameter m: Is P|fixj;pj=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p67_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p67) (lift (Ops.m ZooParallel.p67))

/-- `P|fixj;pj=1|ΣwjUj`, parameter m: Is P|fixj;pj=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p67_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p67) 1 (lift (Ops.m ZooParallel.p67))

/-- `P|fixj;pj=1|ΣTj`, parameter m: Is P|fixj;pj=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p68_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p68) (lift (Ops.m ZooParallel.p68))

/-- `P|fixj;pj=1|ΣTj`, parameter m: Is P|fixj;pj=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p68_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p68) 1 (lift (Ops.m ZooParallel.p68))

/-- `F|fixj;rj;pij=1|Cmax`, parameter m: Is F|fixj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p69_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p69) (lift (Ops.m ZooShops.p69))

/-- `F|fixj;rj;pij=1|Cmax`, parameter m: Is F|fixj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p69_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p69) 1 (lift (Ops.m ZooShops.p69))

/-- `F|fixj;rj;pij=1|ΣCj`, parameter m: Is F|fixj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p70_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p70) (lift (Ops.m ZooShops.p70))

/-- `F|fixj;rj;pij=1|ΣCj`, parameter m: Is F|fixj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p70_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p70) 1 (lift (Ops.m ZooShops.p70))

/-- `F|fixj;pij=1|ΣwjCj`, parameter m: Is F|fixj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p71_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p71) (lift (Ops.m ZooShops.p71))

/-- `F|fixj;pij=1|ΣwjCj`, parameter m: Is F|fixj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p71_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p71) 1 (lift (Ops.m ZooShops.p71))

/-- `F|fixj;pij=1|ΣwjUj`, parameter m: Is F|fixj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p72_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p72) (lift (Ops.m ZooShops.p72))

/-- `F|fixj;pij=1|ΣwjUj`, parameter m: Is F|fixj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p72_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p72) 1 (lift (Ops.m ZooShops.p72))

/-- `F|fixj;pij=1|ΣwjTj`, parameter m: Is F|fixj;pij=1|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p73_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p73) (lift (Ops.m ZooShops.p73))

/-- `F|fixj;pij=1|ΣwjTj`, parameter m: Is F|fixj;pij=1|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p73_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p73) 1 (lift (Ops.m ZooShops.p73))

/-- `O|fixj;rj;pij=1|Cmax`, parameter m: Is O|fixj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p76_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p76) (lift (Ops.m ZooShops.p76))

/-- `O|fixj;rj;pij=1|Cmax`, parameter m: Is O|fixj;rj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p76_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p76) 1 (lift (Ops.m ZooShops.p76))

/-- `O|fixj;rj;pij=1|ΣCj`, parameter m: Is O|fixj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p77_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p77) (lift (Ops.m ZooShops.p77))

/-- `O|fixj;rj;pij=1|ΣCj`, parameter m: Is O|fixj;rj;pij=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p77_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p77) 1 (lift (Ops.m ZooShops.p77))

/-- `O|fixj;pij=1|ΣwjCj`, parameter m: Is O|fixj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p78_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p78) (lift (Ops.m ZooShops.p78))

/-- `O|fixj;pij=1|ΣwjCj`, parameter m: Is O|fixj;pij=1|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p78_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p78) 1 (lift (Ops.m ZooShops.p78))

/-- `O|fixj;pij=1|ΣwjUj`, parameter m: Is O|fixj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p79_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p79) (lift (Ops.m ZooShops.p79))

/-- `O|fixj;pij=1|ΣwjUj`, parameter m: Is O|fixj;pij=1|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p79_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p79) 1 (lift (Ops.m ZooShops.p79))

/-- `O|fixj;pij=1|ΣTj`, parameter m: Is O|fixj;pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p80_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p80) (lift (Ops.m ZooShops.p80))

/-- `O|fixj;pij=1|ΣTj`, parameter m: Is O|fixj;pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p80_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p80) 1 (lift (Ops.m ZooShops.p80))

/-- `O|pij=1;rj|ΣCj`, parameter m: Is O|pij=1;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p91_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p91) (lift (Ops.m ZooShops.p91))

/-- `O|pij=1;rj|ΣCj`, parameter m: Is O|pij=1;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p91_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p91) 1 (lift (Ops.m ZooShops.p91))

/-- `P|pj=p;sizej|ΣwjUj`, parameter m: Is P|pj=p;sizej|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p76_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p76) (lift (Ops.m ZooParallel.p76))

/-- `P|pj=p;sizej|ΣwjUj`, parameter m: Is P|pj=p;sizej|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p76_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p76) 1 (lift (Ops.m ZooParallel.p76))

/-- `P|pj=p;sizej|ΣTj`, parameter m: Is P|pj=p;sizej|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p77_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p77) (lift (Ops.m ZooParallel.p77))

/-- `P|pj=p;sizej|ΣTj`, parameter m: Is P|pj=p;sizej|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p77_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p77) 1 (lift (Ops.m ZooParallel.p77))

/-- `J|n=k;pmtn|Cmax`, parameter m: Is J|n=k;pmtn|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptiveShops_p0_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptiveShops.p0) (lift (Ops.m ZooPreemptiveShops.p0))

/-- `J|n=k;pmtn|Cmax`, parameter m: Is J|n=k;pmtn|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptiveShops_p0_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptiveShops.p0) 1 (lift (Ops.m ZooPreemptiveShops.p0))

/-- `J|n=k;pmtn|ΣCj`, parameter m: Is J|n=k;pmtn|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptiveShops_p1_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptiveShops.p1) (lift (Ops.m ZooPreemptiveShops.p1))

/-- `J|n=k;pmtn|ΣCj`, parameter m: Is J|n=k;pmtn|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptiveShops_p1_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptiveShops.p1) 1 (lift (Ops.m ZooPreemptiveShops.p1))

/-- `P|pj=p;tree|Cmax`, parameter m: Is P|pj=p;tree|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p90_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p90) (lift (Ops.m ZooParallel.p90))

/-- `P|pj=p;tree|Cmax`, parameter m: Is P|pj=p;tree|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p90_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p90) 1 (lift (Ops.m ZooParallel.p90))

/-- `P|pmtn;pj=1;sizej|Cmax`, parameter m: Is P|pmtn;pj=1;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p22_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p22) (lift (Ops.m ZooPreemptive.p22))

/-- `P|pmtn;pj=1;sizej|Cmax`, parameter m: Is P|pmtn;pj=1;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p22_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p22) 1 (lift (Ops.m ZooPreemptive.p22))

/-- `P|pj=p;sizej|ΣwjCj`, parameter m: Is P|pj=p;sizej|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p91_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p91) (lift (Ops.m ZooParallel.p91))

/-- `P|pj=p;sizej|ΣwjCj`, parameter m: Is P|pj=p;sizej|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p91_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p91) 1 (lift (Ops.m ZooParallel.p91))

/-- `P|pj=1;sizej|ΣCj`, parameter m: Is P|pj=1;sizej|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p92_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p92) (lift (Ops.m ZooParallel.p92))

/-- `P|pj=1;sizej|ΣCj`, parameter m: Is P|pj=1;sizej|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p92_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p92) 1 (lift (Ops.m ZooParallel.p92))

/-- `Q|pj=1;rj|ΣCj`, parameter m: Is Q|pj=1;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p98_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p98) (lift (Ops.m ZooParallel.p98))

/-- `Q|pj=1;rj|ΣCj`, parameter m: Is Q|pj=1;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p98_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p98) 1 (lift (Ops.m ZooParallel.p98))

/-- `Q|pj=p;rj|ΣCj`, parameter m: Is Q|pj=p;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p99_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p99) (lift (Ops.m ZooParallel.p99))

/-- `Q|pj=p;rj|ΣCj`, parameter m: Is Q|pj=p;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p99_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p99) 1 (lift (Ops.m ZooParallel.p99))

/-- `P|pj=p;outtree|ΣCj`, parameter m: Is P|pj=p;outtree|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p108_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p108) (lift (Ops.m ZooParallel.p108))

/-- `P|pj=p;outtree|ΣCj`, parameter m: Is P|pj=p;outtree|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p108_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p108) 1 (lift (Ops.m ZooParallel.p108))

/-- `P|fixj;pj=1|Cmax`, parameter m: Is P|fixj;pj=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p120_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p120) (lift (Ops.m ZooParallel.p120))

/-- `P|fixj;pj=1|Cmax`, parameter m: Is P|fixj;pj=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p120_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p120) 1 (lift (Ops.m ZooParallel.p120))

/-- `P|fixj;pj=1|ΣCj`, parameter m: Is P|fixj;pj=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p123_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p123) (lift (Ops.m ZooParallel.p123))

/-- `P|fixj;pj=1|ΣCj`, parameter m: Is P|fixj;pj=1|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p123_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p123) 1 (lift (Ops.m ZooParallel.p123))

/-- `O|Mj;pij=1|Cmax`, parameter m: Is O|Mj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p148_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p148) (lift (Ops.m ZooShops.p148))

/-- `O|Mj;pij=1|Cmax`, parameter m: Is O|Mj;pij=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p148_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p148) 1 (lift (Ops.m ZooShops.p148))

/-- `1||ΣwjUj`, parameter #w: Is 1||ΣwjUj fixed-parameter tractable for #w, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p124_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p124) (lift (Ops.numW ZooParallel.p124))

/-- `1||ΣwjUj`, parameter #w: Is 1||ΣwjUj fixed-parameter tractable for #w, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p124_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p124) 1 (lift (Ops.numW ZooParallel.p124))

/-- `P|fixj;pmtn|Cmax`, parameter m: Is P|fixj;pmtn|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p33_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p33) (lift (Ops.m ZooPreemptive.p33))

/-- `P|fixj;pmtn|Cmax`, parameter m: Is P|fixj;pmtn|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p33_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p33) 1 (lift (Ops.m ZooPreemptive.p33))

/-- `F|fixj;prec;rj;n=k|ΣwjUj`, parameter m: Is F|fixj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p150_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p150) (lift (Ops.m ZooShops.p150))

/-- `F|fixj;prec;rj;n=k|ΣwjUj`, parameter m: Is F|fixj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p150_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p150) 1 (lift (Ops.m ZooShops.p150))

/-- `F|fixj;prec;rj;n=k|ΣwjTj`, parameter m: Is F|fixj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p151_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p151) (lift (Ops.m ZooShops.p151))

/-- `F|fixj;prec;rj;n=k|ΣwjTj`, parameter m: Is F|fixj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p151_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p151) 1 (lift (Ops.m ZooShops.p151))

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjUj`, parameter m: Is O|fixj;prec;rj;pij=1;n=2|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p152_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p152) (lift (Ops.m ZooShops.p152))

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjUj`, parameter m: Is O|fixj;prec;rj;pij=1;n=2|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p152_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p152) 1 (lift (Ops.m ZooShops.p152))

/-- `O|fixj;prec;rj;n=k|ΣwjUj`, parameter m: Is O|fixj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p153_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p153) (lift (Ops.m ZooShops.p153))

/-- `O|fixj;prec;rj;n=k|ΣwjUj`, parameter m: Is O|fixj;prec;rj;n=k|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p153_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p153) 1 (lift (Ops.m ZooShops.p153))

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjTj`, parameter m: Is O|fixj;prec;rj;pij=1;n=2|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p154_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p154) (lift (Ops.m ZooShops.p154))

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjTj`, parameter m: Is O|fixj;prec;rj;pij=1;n=2|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p154_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p154) 1 (lift (Ops.m ZooShops.p154))

/-- `O|fixj;prec;rj;n=k|ΣwjTj`, parameter m: Is O|fixj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p155_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p155) (lift (Ops.m ZooShops.p155))

/-- `O|fixj;prec;rj;n=k|ΣwjTj`, parameter m: Is O|fixj;prec;rj;n=k|ΣwjTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p155_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p155) 1 (lift (Ops.m ZooShops.p155))

/-- `O|pij=1;no-wait|ΣwjUj`, parameter m: Is O|pij=1;no-wait|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p176_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p176) (lift (Ops.m ZooShops.p176))

/-- `O|pij=1;no-wait|ΣwjUj`, parameter m: Is O|pij=1;no-wait|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p176_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p176) 1 (lift (Ops.m ZooShops.p176))

/-- `O|pij=1;rj|ΣUj`, parameter m: Is O|pij=1;rj|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p180_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p180) (lift (Ops.m ZooShops.p180))

/-- `O|pij=1;rj|ΣUj`, parameter m: Is O|pij=1;rj|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p180_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p180) 1 (lift (Ops.m ZooShops.p180))

/-- `P|pmtn|ΣwjCj`, parameter m: Is P|pmtn|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p39_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p39) (lift (Ops.m ZooPreemptive.p39))

/-- `P|pmtn|ΣwjCj`, parameter m: Is P|pmtn|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p39_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p39) 1 (lift (Ops.m ZooPreemptive.p39))

/-- `Q|pmtn|ΣUj`, parameter m: Is Q|pmtn|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p40_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p40) (lift (Ops.m ZooPreemptive.p40))

/-- `Q|pmtn|ΣUj`, parameter m: Is Q|pmtn|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p40_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p40) 1 (lift (Ops.m ZooPreemptive.p40))

/-- `Q|pmtn|ΣwjUj`, parameter m: Is Q|pmtn|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p41_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p41) (lift (Ops.m ZooPreemptive.p41))

/-- `Q|pmtn|ΣwjUj`, parameter m: Is Q|pmtn|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p41_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p41) 1 (lift (Ops.m ZooPreemptive.p41))

/-- `P|pj=1;sizej|Cmax`, parameter m: Is P|pj=1;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p138_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p138) (lift (Ops.m ZooParallel.p138))

/-- `P|pj=1;sizej|Cmax`, parameter m: Is P|pj=1;sizej|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p138_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p138) 1 (lift (Ops.m ZooParallel.p138))

/-- `P|pmtn|ΣUj`, parameter m: Is P|pmtn|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p45_q2_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p45) (lift (Ops.m ZooPreemptive.p45))

/-- `P|pmtn|ΣUj`, parameter m: Is P|pmtn|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p45_q2_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p45) 1 (lift (Ops.m ZooPreemptive.p45))

/-- `O|pij=1|ΣUj`, parameter m: Is O|pij=1|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p191_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p191) (lift (Ops.m ZooShops.p191))

/-- `O|pij=1|ΣUj`, parameter m: Is O|pij=1|ΣUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p191_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p191) 1 (lift (Ops.m ZooShops.p191))

/-- `O|pij=1|ΣTj`, parameter m: Is O|pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p192_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p192) (lift (Ops.m ZooShops.p192))

/-- `O|pij=1|ΣTj`, parameter m: Is O|pij=1|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p192_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p192) 1 (lift (Ops.m ZooShops.p192))

/-- `Q||ΣwjUj`, parameter m: Is Q||ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p147_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p147) (lift (Ops.m ZooParallel.p147))

/-- `Q||ΣwjUj`, parameter m: Is Q||ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p147_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p147) 1 (lift (Ops.m ZooParallel.p147))

/-- `P|pj=1;bounded height|Cmax`, parameter m: Is P|pj=1;bounded height|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p150_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p150) (lift (Ops.m ZooParallel.p150))

/-- `P|pj=1;bounded height|Cmax`, parameter m: Is P|pj=1;bounded height|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p150_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p150) 1 (lift (Ops.m ZooParallel.p150))

/-- `P|pj=p;pmtn|ΣwjCj`, parameter m: Is P|pj=p;pmtn|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p54_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooPreemptive.p54) (lift (Ops.m ZooPreemptive.p54))

/-- `P|pj=p;pmtn|ΣwjCj`, parameter m: Is P|pj=p;pmtn|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooPreemptive_p54_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooPreemptive.p54) 1 (lift (Ops.m ZooPreemptive.p54))

/-- `1||ΣUj`, parameter #p: Is 1||ΣUj fixed-parameter tractable for #p, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p164_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p164) (lift (Ops.numP ZooParallel.p164))

/-- `1||ΣUj`, parameter #p: Is 1||ΣUj fixed-parameter tractable for #p, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p164_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p164) 1 (lift (Ops.numP ZooParallel.p164))

/-- `1||ΣUj`, parameter #w: Is 1||ΣUj fixed-parameter tractable for #w, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p164_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p164) (lift (Ops.numW ZooParallel.p164))

/-- `1||ΣUj`, parameter #w: Is 1||ΣUj fixed-parameter tractable for #w, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p164_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p164) 1 (lift (Ops.numW ZooParallel.p164))

/-- `P|pj=p;rj|ΣCj`, parameter m: Is P|pj=p;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p171_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p171) (lift (Ops.m ZooParallel.p171))

/-- `P|pj=p;rj|ΣCj`, parameter m: Is P|pj=p;rj|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p171_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p171) 1 (lift (Ops.m ZooParallel.p171))

/-- `O|pij=1;rj;no-wait|ΣCj`, parameter m: Is O|pij=1;rj;no-wait|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p268_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p268) (lift (Ops.m ZooShops.p268))

/-- `O|pij=1;rj;no-wait|ΣCj`, parameter m: Is O|pij=1;rj;no-wait|ΣCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p268_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p268) 1 (lift (Ops.m ZooShops.p268))

/-- `O|pij=1;rj;no-wait|ΣwjCj`, parameter m: Is O|pij=1;rj;no-wait|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p272_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p272) (lift (Ops.m ZooShops.p272))

/-- `O|pij=1;rj;no-wait|ΣwjCj`, parameter m: Is O|pij=1;rj;no-wait|ΣwjCj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p272_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p272) 1 (lift (Ops.m ZooShops.p272))

/-- `O|pij=1;rj;no-wait|ΣTj`, parameter m: Is O|pij=1;rj;no-wait|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p273_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooShops.p273) (lift (Ops.m ZooShops.p273))

/-- `O|pij=1;rj;no-wait|ΣTj`, parameter m: Is O|pij=1;rj;no-wait|ΣTj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooShops_p273_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooShops.p273) 1 (lift (Ops.m ZooShops.p273))

/-- `P|pj=p|ΣwjUj`, parameter pmax: Is P|pj=p|ΣwjUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p182_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p182) (lift (Ops.pmax ZooParallel.p182))

/-- `P|pj=p|ΣwjUj`, parameter pmax: Is P|pj=p|ΣwjUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p182_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p182) 1 (lift (Ops.pmax ZooParallel.p182))

/-- `P|pj=p|ΣwjUj`, parameter m: Is P|pj=p|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p182_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p182) (lift (Ops.m ZooParallel.p182))

/-- `P|pj=p|ΣwjUj`, parameter m: Is P|pj=p|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p182_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p182) 1 (lift (Ops.m ZooParallel.p182))

/-- `Q|pj=p;rj|Cmax`, parameter m: Is Q|pj=p;rj|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p187_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p187) (lift (Ops.m ZooParallel.p187))

/-- `Q|pj=p;rj|Cmax`, parameter m: Is Q|pj=p;rj|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p187_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p187) 1 (lift (Ops.m ZooParallel.p187))

/-- `Q|pj=p|ΣwjUj`, parameter m: Is Q|pj=p|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p188_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p188) (lift (Ops.m ZooParallel.p188))

/-- `Q|pj=p|ΣwjUj`, parameter m: Is Q|pj=p|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p188_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p188) 1 (lift (Ops.m ZooParallel.p188))

/-- `P|pj=1;rj|ΣwjUj`, parameter pmax: Is P|pj=1;rj|ΣwjUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p190_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p190) (lift (Ops.pmax ZooParallel.p190))

/-- `P|pj=1;rj|ΣwjUj`, parameter pmax: Is P|pj=1;rj|ΣwjUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p190_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p190) 1 (lift (Ops.pmax ZooParallel.p190))

/-- `P|pj=1;rj|ΣwjUj`, parameter m: Is P|pj=1;rj|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p190_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p190) (lift (Ops.m ZooParallel.p190))

/-- `P|pj=1;rj|ΣwjUj`, parameter m: Is P|pj=1;rj|ΣwjUj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p190_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p190) 1 (lift (Ops.m ZooParallel.p190))

/-- `P|Mj|ΣZj`, parameter m: Is P|Mj|ΣZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p201_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p201) (lift (Ops.m ZooParallel.p201))

/-- `P|Mj|ΣZj`, parameter m: Is P|Mj|ΣZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p201_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p201) 1 (lift (Ops.m ZooParallel.p201))

/-- `P||ΣwjZj`, parameter m: Is P||ΣwjZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p202_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p202) (lift (Ops.m ZooParallel.p202))

/-- `P||ΣwjZj`, parameter m: Is P||ΣwjZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p202_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p202) 1 (lift (Ops.m ZooParallel.p202))

/-- `P|Mj;pj=p|ΣZj`, parameter m: Is P|Mj;pj=p|ΣZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p203_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p203) (lift (Ops.m ZooParallel.p203))

/-- `P|Mj;pj=p|ΣZj`, parameter m: Is P|Mj;pj=p|ΣZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p203_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p203) 1 (lift (Ops.m ZooParallel.p203))

/-- `P|Mj;pj=p|ΣwjZj`, parameter m: Is P|Mj;pj=p|ΣwjZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p204_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p204) (lift (Ops.m ZooParallel.p204))

/-- `P|Mj;pj=p|ΣwjZj`, parameter m: Is P|Mj;pj=p|ΣwjZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p204_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p204) 1 (lift (Ops.m ZooParallel.p204))

/-- `P||ΣZj`, parameter m: Is P||ΣZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p206_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p206) (lift (Ops.m ZooParallel.p206))

/-- `P||ΣZj`, parameter m: Is P||ΣZj fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p206_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p206) 1 (lift (Ops.m ZooParallel.p206))

/-- `P|opposing forest;pj=p|Cmax`, parameter m: Is P|opposing forest;pj=p|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p211_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p211) (lift (Ops.m ZooParallel.p211))

/-- `P|opposing forest;pj=p|Cmax`, parameter m: Is P|opposing forest;pj=p|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p211_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p211) 1 (lift (Ops.m ZooParallel.p211))

/-- `P|opposing forest;pj=1|Cmax`, parameter m: Is P|opposing forest;pj=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p212_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p212) (lift (Ops.m ZooParallel.p212))

/-- `P|opposing forest;pj=1|Cmax`, parameter m: Is P|opposing forest;pj=1|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p212_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p212) 1 (lift (Ops.m ZooParallel.p212))

/-- `P|bounded height;pj=p|Cmax`, parameter m: Is P|bounded height;pj=p|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p213_q0_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p213) (lift (Ops.m ZooParallel.p213))

/-- `P|bounded height;pj=p|Cmax`, parameter m: Is P|bounded height;pj=p|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p213_q0_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p213) 1 (lift (Ops.m ZooParallel.p213))

/-- `P|level order;pj=p|Cmax`, parameter m: Is P|level order;pj=p|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p214_q1_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p214) (lift (Ops.m ZooParallel.p214))

/-- `P|level order;pj=p|Cmax`, parameter m: Is P|level order;pj=p|Cmax fixed-parameter tractable for m, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p214_q1_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p214) 1 (lift (Ops.m ZooParallel.p214))

/-- `P|rj;pj=p|ΣUj`, parameter pmax: Is P|rj;pj=p|ΣUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p238_q2_yes (R : Reading OperationsFamily.family) : Prop :=
  IsFPT (R.at ZooParallel.p238) (lift (Ops.pmax ZooParallel.p238))

/-- `P|rj;pj=p|ΣUj`, parameter pmax: Is P|rj;pj=p|ΣUj fixed-parameter tractable for pmax, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooParallel_p238_q2_no (R : Reading OperationsFamily.family) : Prop :=
  WHard (R.at ZooParallel.p238) 1 (lift (Ops.pmax ZooParallel.p238))

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #d+#p+#w: Is 1|s-batch(∞);rj|ΣwjUj fixed-parameter tractable for #d+#p+#w, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p19_q1_yes (R : Reading BatchFamily.family) : Prop :=
  IsFPT (R.at ZooSerialBatching.p19) (tplus (tplus (lift (Batch.numD ZooSerialBatching.p19)) (lift (Batch.numP ZooSerialBatching.p19))) (lift (Batch.numW ZooSerialBatching.p19)))

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #d+#p+#w: Is 1|s-batch(∞);rj|ΣwjUj fixed-parameter tractable for #d+#p+#w, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p19_q1_no (R : Reading BatchFamily.family) : Prop :=
  WHard (R.at ZooSerialBatching.p19) 1 (tplus (tplus (lift (Batch.numD ZooSerialBatching.p19)) (lift (Batch.numP ZooSerialBatching.p19))) (lift (Batch.numW ZooSerialBatching.p19)))

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #p+#r+#w: Is 1|s-batch(∞);rj|ΣwjUj fixed-parameter tractable for #p+#r+#w, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p19_q2_yes (R : Reading BatchFamily.family) : Prop :=
  IsFPT (R.at ZooSerialBatching.p19) (tplus (tplus (lift (Batch.numP ZooSerialBatching.p19)) (lift (Batch.numR ZooSerialBatching.p19))) (lift (Batch.numW ZooSerialBatching.p19)))

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #p+#r+#w: Is 1|s-batch(∞);rj|ΣwjUj fixed-parameter tractable for #p+#r+#w, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p19_q2_no (R : Reading BatchFamily.family) : Prop :=
  WHard (R.at ZooSerialBatching.p19) 1 (tplus (tplus (lift (Batch.numP ZooSerialBatching.p19)) (lift (Batch.numR ZooSerialBatching.p19))) (lift (Batch.numW ZooSerialBatching.p19)))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #p: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #p, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q1_yes (R : Reading BatchFamily.family) : Prop :=
  IsFPT (R.at ZooSerialBatching.p20) (lift (Batch.numP ZooSerialBatching.p20))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #p: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #p, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q1_no (R : Reading BatchFamily.family) : Prop :=
  WHard (R.at ZooSerialBatching.p20) 1 (lift (Batch.numP ZooSerialBatching.p20))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #w: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #w, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q2_yes (R : Reading BatchFamily.family) : Prop :=
  IsFPT (R.at ZooSerialBatching.p20) (lift (Batch.numW ZooSerialBatching.p20))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #w: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #w, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q2_no (R : Reading BatchFamily.family) : Prop :=
  WHard (R.at ZooSerialBatching.p20) 1 (lift (Batch.numW ZooSerialBatching.p20))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #d+#p+#w: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #d+#p+#w, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q3_yes (R : Reading BatchFamily.family) : Prop :=
  IsFPT (R.at ZooSerialBatching.p20) (tplus (tplus (lift (Batch.numD ZooSerialBatching.p20)) (lift (Batch.numP ZooSerialBatching.p20))) (lift (Batch.numW ZooSerialBatching.p20)))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #d+#p+#w: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #d+#p+#w, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q3_no (R : Reading BatchFamily.family) : Prop :=
  WHard (R.at ZooSerialBatching.p20) 1 (tplus (tplus (lift (Batch.numD ZooSerialBatching.p20)) (lift (Batch.numP ZooSerialBatching.p20))) (lift (Batch.numW ZooSerialBatching.p20)))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #p+#r+#w: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #p+#r+#w, or W[1]-hard? It is in XP.

The yes side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q4_yes (R : Reading BatchFamily.family) : Prop :=
  IsFPT (R.at ZooSerialBatching.p20) (tplus (tplus (lift (Batch.numP ZooSerialBatching.p20)) (lift (Batch.numR ZooSerialBatching.p20))) (lift (Batch.numW ZooSerialBatching.p20)))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #p+#r+#w: Is 1|s-batch(∞)|ΣwjUj fixed-parameter tractable for #p+#r+#w, or W[1]-hard? It is in XP.

The no side. Source: the zoo's data, own and inherited results.
-/
def ZooSerialBatching_p20_q4_no (R : Reading BatchFamily.family) : Prop :=
  WHard (R.at ZooSerialBatching.p20) 1 (tplus (tplus (lift (Batch.numP ZooSerialBatching.p20)) (lift (Batch.numR ZooSerialBatching.p20))) (lift (Batch.numW ZooSerialBatching.p20)))

end Lax434175.ZooOpen
