import Lax434175.ZooPreemptive
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, preemptive problems on parallel machines
type: definition
---
The 95 results of The Scheduling Zoo on its preemptive problems on parallel machines that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooPreemptiveResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters Lax434175.ZooPreemptive

/-- `R|rj;pmtn|ΣwjCj`: has a polynomial time approximation ratio < 1.99971 by LP-rounding.

Sungjin Im and Shi Li (2017). Better Unrelated Machine Scheduling for Weighted Completion Time via Random sets from Non-Uniform Distributions. https://doi.org/10.1109/focs.2016.23
-/
def p0_r0 (R : Reading F) : Prop :=
  ∃ ρ : ℝ, ρ < (1.99971 : ℝ) ∧ Approx (R.at p0) (const ρ)

/-- `R|rj;pmtn|ΣwjCj`: has a 3-approximation algorithm when migration is allowed.

Skutella, Martin (2001). Convex Quadratic and Semidefinite Programming Relaxations in Scheduling. https://doi.org/10.1145/375827.375840

Note: preemption lets a job move between machines, as in the source.
-/
def p0_r1 (R : Reading F) : Prop :=
  Approx (R.at p0) (const (3 : ℝ))

/-- `R|rj;pmtn|ΣwjCj`, parameter m: has a PTAS.

Afrati, Foto and Bampis, Evripidis and Chekuri, Chandra and Karger, David and Kenyon, Claire and Khanna, Sanjeev and Milis, Ioannis and Queyranne, Maurice and Skutella, Martin and Stein, Clifford and others (1999). Approximation schemes for minimizing average weighted completion time with release dates. https://doi.org/10.1109/sffcs.1999.814574

Note: a PTAS for every fixed value.
-/
def p0_r2 (R : Reading F) : Prop :=
  PTASFixed (R.at p0) (Ops.m p0)

/-- `1|prec;rj;pmtn|Lmax`: is in P.

Błażewicz, J. (1976). Scheduling dependent tasks with different arrival times to meet deadlines. None
-/
def p1_r0 (R : Reading F) : Prop :=
  InP (R.at p1)

/-- `1|prec;rj;pmtn|Lmax`: is in P.

Baker, K.R. and Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1983). Preemptive scheduling of a single machine to minimize maximum cost subject to release dates and precedence constraints. https://doi.org/10.1287/opre.31.2.381
-/
def p1_r1 (R : Reading F) : Prop :=
  InP (R.at p1)

/-- `P|pj=p;pmtn|ΣwjUj`: is NP-hard.

Brucker, P. and Kravchenko, S.A. (1999). Preemption can make parallel machine scheduling problems hard. None
-/
def p2_r0 (R : Reading F) : Prop :=
  NPHard (R.at p2)

/-- `P|pj=p;pmtn|ΣwjUj`, parameter m: is in P.

Baptiste, P. (2000). Preemptive scheduling of identical machines. None

Note: in P for every fixed value.
-/
def p2_r1 (R : Reading F) : Prop :=
  InPFixed (R.at p2) (lift (Ops.m p2))

/-- `P|pj=1;pmtn;rj|ΣwjTj`: is in P.

Baptiste, P. (2002). On preemption redundancy. https://doi.org/10.1109/ipdps.2001.925215
-/
def p3_r0 (R : Reading F) : Prop :=
  InP (R.at p3)

/-- `1|rj;pmtn|ΣCj`: is in P.

Baker, K.R. (1974). Introduction to Sequencing and Scheduling. None
-/
def p4_r0 (R : Reading F) : Prop :=
  InP (R.at p4)

/-- `1|rj;pmtn|ΣCj`: randomized approximation ratio using alpha-points ≤4/3.

Skutella, Martin (2006). List scheduling in order of $\alpha$-points on a single machine. https://doi.org/10.1007/11671541_9
-/
def p4_r1 (R : Reading F) : Prop :=
  RandomApprox (R.at p4) (const ((4 : ℝ) / 3))

/-- `1|pmtn;pj=p;rj|ΣwjUj`: is in P.

Baptiste, P. (1999). Polynomial time algorithms for minimizing the weighted number of late jobs on a single machine with equal processing times. https://doi.org/10.1002/(sici)1099-1425(199911/12)2:6<245::aid-jos28>3.0.co;2-5
-/
def p5_r0 (R : Reading F) : Prop :=
  InP (R.at p5)

/-- `1|pmtn;pj=p;rj|ΣwjUj`: is solvable in O(n^4).

Baptiste, Philippe and Chrobak, Marek and Dürr, Christoph and Jawor, Wojciech and Vakhania, Nodari (2004). Preemptive scheduling of equal-length jobs to maximize weighted throughput. https://doi.org/10.1016/j.orl.2003.09.004
-/
def p5_r1 (R : Reading F) : Prop :=
  DecidesWithin (R.at p5) (fun x => (Ops.n p5 x) ^ 4)

/-- `1|prec;rj;pj=p;pmtn|ΣCj`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p6_r0 (R : Reading F) : Prop :=
  InP (R.at p6)

/-- `P|pj=p;pmtn|ΣCj`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p7_r0 (R : Reading F) : Prop :=
  InP (R.at p7)

/-- `Q|pj=p;pmtn|ΣUj`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p8_r0 (R : Reading F) : Prop :=
  InP (R.at p8)

/-- `P2|pj=1;chains;pmtn|ΣUj`: is strongly NP-hard.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p9_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p9)

/-- `P|fixj;rj;pmtn|Lmax`, parameter m: is in P.

Bianco, L. and Błażewicz, J. and Dell'Olmo, P. and Drozdowski, M. (1997). Preemptive multiprocessor task scheduling with release times and time windows. https://doi.org/10.1023/a:1018994726051

Note: in P for every fixed value.
-/
def p10_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p10) (lift (Ops.m p10))

/-- `P2|pmtn|ΣwjCj`: is NP-hard.

Bruno, J. and Coffman, Jr., E.G. and Sethi, R. (1974). Scheduling independent tasks to reduce mean finishing time. https://doi.org/10.1145/361011.361064
-/
def p11_r0 (R : Reading F) : Prop :=
  NPHard (R.at p11)

/-- `P|pmtn;rj;sizej|Lmax`, parameter m: is in P.

Błażewicz, J. and Drozdowski, M. and de Werra, D. and Wȩglarz, J. (1996). Deadline scheduling of multiprocessor tasks. https://doi.org/10.1016/0166-218x(95)00020-r

Note: in P for every fixed value.
-/
def p12_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p12) (lift (Ops.m p12))

/-- `P|pj=1;pmtn;rj|ΣwjUj`: is in P.

Brucker, P. and Heitmann, S. and Hurink, J. (2003). How useful are preemptive schedules?. https://doi.org/10.1016/s0167-6377(02)00220-1
-/
def p13_r0 (R : Reading F) : Prop :=
  InP (R.at p13)

/-- `P2|pj=1;pmtn;rj|ΣwjTj`: is in P.

Brucker, P. and Heitmann, S. and Hurink, J. (2003). How useful are preemptive schedules?. https://doi.org/10.1016/s0167-6377(02)00220-1
-/
def p14_r0 (R : Reading F) : Prop :=
  InP (R.at p14)

/-- `P|pj=1;outtree;rj;pmtn|ΣCj`: is in P.

Brucker, P. and Hurink, J. and Knust, S. (2002). A polynomial algorithm for $P|p_j=1, r_j, outtree|\sumC_j$. None
-/
def p15_r0 (R : Reading F) : Prop :=
  InP (R.at p15)

/-- `P|pj=1;outtree;rj;pmtn|ΣCj`: is in P.

Huo, Y. and Leung, J.Y.-T. (2005). Minimizing total completion time for UET tasks with release time and outtree precedence constraints. https://doi.org/10.1007/s00186-005-0009-5
-/
def p15_r1 (R : Reading F) : Prop :=
  InP (R.at p15)

/-- `P|pj=p;outtree;pmtn|ΣCj`: is in P.

Brucker, P. and Hurink, J. and Knust, S. (2002). A polynomial algorithm for $P|p_j=1, r_j, outtree|\sumC_j$. None
-/
def p16_r0 (R : Reading F) : Prop :=
  InP (R.at p16)

/-- `P|pj=p;outtree;pmtn|ΣCj`: is in P.

Huo, Y. and Leung, J.Y.-T. (2005). Minimizing total completion time for UET tasks with release time and outtree precedence constraints. https://doi.org/10.1007/s00186-005-0009-5
-/
def p16_r1 (R : Reading F) : Prop :=
  InP (R.at p16)

/-- `P|rj;pmtn;pj=p|ΣCj`: is solvable by a linear program of size O(nm).

Philippe Baptiste and Peter Brucker and Marek Chrobak and Christoph Dürr and Svetlana A. Kravchenko and Francis Sourd (to appear). The Complexity of Mean Flow Time Scheduling Problems with Release Times. https://doi.org/10.1007/s10951-006-0006-4

Note: the size of the linear program is not stated; solving it gives polynomial time.
-/
def p17_r0 (R : Reading F) : Prop :=
  InP (R.at p17)

/-- `P|rj;pmtn;pj=p|ΣCj`: is in P.

Brucker, P. and Kravchenko, S.A. (2004). Complexity of mean flow time scheduling problems with release dates. None
-/
def p17_r1 (R : Reading F) : Prop :=
  InP (R.at p17)

/-- `P|rj;pmtn|ΣCj`: is strongly NP-hard.

Odile Bellenguez-Morineau and Marek Chrobak and Christoph Dürr and Damien Prot (2015). A Note on NP-Hardness of Preemptive Mean Flow-Time Scheduling for Parallel Machines. https://doi.org/10.1007/s10951-014-0380-2
-/
def p18_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p18)

/-- `P|rj;pmtn|ΣCj`: is strongly NP-hard.

Brucker, P. and Kravchenko, S.A. (2004). Complexity of mean flow time scheduling problems with release dates. None
-/
def p18_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p18)

/-- `P2|pmtn;outtree;rj;pj=1|ΣCj`: is in P.

Baptiste, P. and Timkovsky, V. (2001). On preemption redundancy in scheduling unit processing time jobs on two parallel machines. https://doi.org/10.1109/ipdps.2001.925215
-/
def p19_r0 (R : Reading F) : Prop :=
  InP (R.at p19)

/-- `P2|fixj;pmtn|ΣCj`: is in P.

Cai, X. and Lee, C.-Y. and Li, C.-L. (1998). Minimizing total completion time in two-processor task systems with prespecified processor allocations. https://doi.org/10.1002/(sici)1520-6750(199803)45:2<231::aid-nav7>3.3.co;2-0
-/
def p20_r0 (R : Reading F) : Prop :=
  InP (R.at p20)

/-- `P2|pj=1;pmtn;prec|ΣCj`: is in P.

Coffman, Jr., E.G. and Sethuraman, J. and Timkovsky, V.G. (2003). Ideal preemptive schedules on two processors. https://doi.org/10.1007/s00236-003-0119-6
-/
def p21_r0 (R : Reading F) : Prop :=
  InP (R.at p21)

/-- `P|pmtn;pj=1;sizej|Cmax`: is NP-hard.

Drozdowski, M. (1992). Problems and algorithms of multiprocessor tasks scheduling. None
-/
def p22_r0 (R : Reading F) : Prop :=
  NPHard (R.at p22)

/-- `P|pmtn;sizej|ΣCj`: is NP-hard.

Drozdowski, M. and Dell' Olmo, P. (2000). Scheduling multiprocessor tasks for mean flow time criterion. https://doi.org/10.1016/s0305-0548(99)00048-9
-/
def p23_r0 (R : Reading F) : Prop :=
  NPHard (R.at p23)

/-- `R|pmtn;rj|ΣUj`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. (1991). Minimizing the number of late jobs on unrelated machines. https://doi.org/10.1016/0167-6377(91)90032-k
-/
def p24_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p24)

/-- `P2|pmtn;rj|ΣUj`: is NP-hard.

Du, J. and Leung, J.Y.-T. and Wong, C.S. (1992). Minimizing the number of late jobs with release time constraint. None
-/
def p25_r0 (R : Reading F) : Prop :=
  NPHard (R.at p25)

/-- `P2|pmtn;rj|ΣCj`: is NP-hard.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1990). Minimizing mean flow time with release time constraint. https://doi.org/10.1016/0304-3975(90)90100-v
-/
def p26_r0 (R : Reading F) : Prop :=
  NPHard (R.at p26)

/-- `P2|pj=p;chains;pmtn|ΣCj`: is in P.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1991). Scheduling chain-structured tasks to minimize makespan and mean flow time. https://doi.org/10.1016/0890-5401(91)90009-q
-/
def p27_r0 (R : Reading F) : Prop :=
  InP (R.at p27)

/-- `P2|pj=p;chains;pmtn|ΣCj`: is in P.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p27_r1 (R : Reading F) : Prop :=
  InP (R.at p27)

/-- `P2|chains;pj=1;pmtn|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p28_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p28)

/-- `P2|chains;pj=1;pmtn|ΣwjCj`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1991). Scheduling chain-structured tasks to minimize makespan and mean flow time. https://doi.org/10.1016/0890-5401(91)90009-q
-/
def p28_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p28)

/-- `P2|chains;pmtn|ΣCj`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1991). Scheduling chain-structured tasks to minimize makespan and mean flow time. https://doi.org/10.1016/0890-5401(91)90009-q
-/
def p29_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p29)

/-- `P|tree;pmtn|Cmax`: is in P.

Gonzalez, T. and Johnson, D.B. (1980). A new algorithm for preemptive scheduling of trees. https://doi.org/10.1145/322186.322194
-/
def p30_r0 (R : Reading F) : Prop :=
  InP (R.at p30)

/-- `P|tree;pmtn|Cmax`: is in P.

Muntz, R.R. and Coffman, Jr., E.G. (1970). Preemptive scheduling of real-time tasks on multiprocessor systems. https://doi.org/10.1145/321574.321586
-/
def p30_r1 (R : Reading F) : Prop :=
  InP (R.at p30)

/-- `P2|pj=p;pmtn;rj|ΣCj`: is in P.

Herrbach, L.A. and Leung, J.Y.-T. (1990). Preemptive scheduling of equal length jobs on two machines to minimize mean flow time. https://doi.org/10.1287/opre.38.3.487
-/
def p31_r0 (R : Reading F) : Prop :=
  InP (R.at p31)

/-- `Q|chains;pmtn|Cmax`: is in P.

Horvath, E.C. and Lam, S. and Sethi, R. (1977). A level algorithm for preemptive scheduling. https://doi.org/10.1145/321992.321995
-/
def p32_r0 (R : Reading F) : Prop :=
  InP (R.at p32)

/-- `P|fixj;pmtn|Cmax`: is strongly NP-hard.

Kubale, M. (1990). Preemptive scheduling of two-processor tasks on dedicated processors. None
-/
def p33_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p33)

/-- `Q|pj=p;rj;pmtn|ΣCj`: is in P.

Kravchenko, S.A. and Werner, F. (2009). Preemptive scheduling on uniform machines to minimize mean flow time. https://doi.org/10.1016/j.cor.2008.12.010
-/
def p34_r0 (R : Reading F) : Prop :=
  InP (R.at p34)

/-- `1|chains;rj;pmtn|ΣCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p35_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p35)

/-- `P|intree;pmtn;rj|Cmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p36_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p36)

/-- `R2|chains;pmtn|Cmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p37_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p37)

/-- `P|outtree;pmtn|Lmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p38_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p38)

/-- `P|pmtn|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p39_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p39)

/-- `P|pmtn|ΣwjCj`, parameter m: is in Ppseudo.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. and Shmoys, D.B. (1989). Sequencing and Scheduling: Algorithms and Complexity. None

Note: pseudo-polynomial for every fixed value.
-/
def p39_r1 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p39) (lift (Ops.m p39))

/-- `P|pmtn|ΣwjCj`, parameter m: is in Ppseudo.

McNaughton, R. (1959). Scheduling with deadlines and loss functions. https://doi.org/10.1287/mnsc.6.1.1

Note: pseudo-polynomial for every fixed value.
-/
def p39_r2 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p39) (lift (Ops.m p39))

/-- `Q|pmtn|ΣUj`, parameter m: is in P.

Lawler, E.L. (1979). Preemptive scheduling of uniform parallel machines to minimize the weighted number of late jobs. None

Note: in P for every fixed value.
-/
def p40_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p40) (lift (Ops.m p40))

/-- `Q|pmtn|ΣUj`, parameter m: is in P.

Lawler, E.L. and Martel, C.U. (1989). Preemptive scheduling of two uniform machines to minimize the number of late jobs. https://doi.org/10.1287/opre.37.2.314

Note: in P for every fixed value.
-/
def p40_r1 (R : Reading F) : Prop :=
  InPFixed (R.at p40) (lift (Ops.m p40))

/-- `Q|pmtn|ΣwjUj`, parameter m: is in Ppseudo.

Lawler, E.L. (1979). Preemptive scheduling of uniform parallel machines to minimize the weighted number of late jobs. None

Note: pseudo-polynomial for every fixed value.
-/
def p41_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p41) (lift (Ops.m p41))

/-- `Q|pmtn|ΣwjUj`, parameter m: is in Ppseudo.

Lawler, E.L. and Martel, C.U. (1989). Preemptive scheduling of two uniform machines to minimize the number of late jobs. https://doi.org/10.1287/opre.37.2.314

Note: pseudo-polynomial for every fixed value.
-/
def p41_r1 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p41) (lift (Ops.m p41))

/-- `P|outtree;pmtn;rj|Cmax`: is in P.

Lawler, E.L. (1982). Preemptive scheduling of precedence-constrained jobs on parallel machines. https://doi.org/10.1007/978-94-009-7801-0_6
-/
def p42_r0 (R : Reading F) : Prop :=
  InP (R.at p42)

/-- `P|intree;pmtn|Lmax`: is in P.

Lawler, E.L. (1982). Preemptive scheduling of precedence-constrained jobs on parallel machines. https://doi.org/10.1007/978-94-009-7801-0_6
-/
def p43_r0 (R : Reading F) : Prop :=
  InP (R.at p43)

/-- `Q2|prec;pmtn;rj|Lmax`: is in P.

Lawler, E.L. (1982). Preemptive scheduling of precedence-constrained jobs on parallel machines. https://doi.org/10.1007/978-94-009-7801-0_6
-/
def p44_r0 (R : Reading F) : Prop :=
  InP (R.at p44)

/-- `P|pmtn|ΣUj`: is NP-hard.

Lawler, E.L. (1983). Recent results in the theory of machine scheduling. https://doi.org/10.1007/978-3-642-68874-4_9
-/
def p45_r0 (R : Reading F) : Prop :=
  NPHard (R.at p45)

/-- `1|rj;pmtn|ΣUj`: is in P.

Lawler, E.L. (1990). A dynamic programming algorithm for preemptive scheduling of a single machine to minimize the number of late jobs. https://doi.org/10.1007/bf02248588
-/
def p46_r0 (R : Reading F) : Prop :=
  InP (R.at p46)

/-- `1|rj;pmtn|ΣwjUj`: is in Ppseudo.

Lawler, E.L. (1990). A dynamic programming algorithm for preemptive scheduling of a single machine to minimize the number of late jobs. https://doi.org/10.1007/bf02248588
-/
def p47_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p47)

/-- `R|pmtn;rj|Lmax`: is in P.

Lawler, E.L. and Labetoulle, J. (1978). On preemptive scheduling of unrelated parallel processors by linear programming. https://doi.org/10.1145/322092.322101
-/
def p48_r0 (R : Reading F) : Prop :=
  InP (R.at p48)

/-- `1|rj;pmtn|ΣwjCj`: is strongly NP-hard.

Labetoulle, J. and Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1984). Preemptive scheduling of uniform machines subject to release dates. https://doi.org/10.1016/b978-0-12-566780-7.50020-9
-/
def p49_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p49)

/-- `1|rj;pmtn|ΣwjCj`: deterministic approximation ratio ≤4/3 based on alpha-points.

Schulz, Andreas S and Skutella, Martin (2002). The power of $\alpha$-points in preemptive single machine scheduling. https://doi.org/10.1002/jos.93
-/
def p49_r1 (R : Reading F) : Prop :=
  Approx (R.at p49) (const ((4 : ℝ) / 3))

/-- `1|rj;pmtn|ΣwjCj`: randomized approximation ratio ≤4/3.

Schulz, Andreas S and Skutella, Martin (1997). Scheduling-LPs bear probabilities randomized approximations for min-sum criteria. https://doi.org/10.1007/3-540-63397-9_32
-/
def p49_r3 (R : Reading F) : Prop :=
  RandomApprox (R.at p49) (const ((4 : ℝ) / 3))

/-- `Q|pmtn|ΣCj`: is in P.

Labetoulle, J. and Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1984). Preemptive scheduling of uniform machines subject to release dates. https://doi.org/10.1016/b978-0-12-566780-7.50020-9
-/
def p50_r0 (R : Reading F) : Prop :=
  InP (R.at p50)

/-- `P2|pmtn;rj|ΣwjCj`: is strongly NP-hard.

Labetoulle, J. and Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1984). Preemptive scheduling of uniform machines subject to release dates. https://doi.org/10.1016/b978-0-12-566780-7.50020-9
-/
def p51_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p51)

/-- `P|pj=p;pmtn;rj|ΣwjCj`: is strongly NP-hard.

Leung, J.Y.-T. and Young, G.H. (1990). Preemptive scheduling to minimize mean weighted flow time. https://doi.org/10.1016/0020-0190(90)90229-q
-/
def p52_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p52)

/-- `P2|pmtn;outtree;pj=p;rj|ΣCj`: is in P.

Lushchakova, I. (2006). Two machine preemptive scheduling problem with release dates, equal processing times and precedence constraints. https://doi.org/10.1016/j.ejor.2004.08.037
-/
def p53_r0 (R : Reading F) : Prop :=
  InP (R.at p53)

/-- `P|pj=p;pmtn|ΣwjCj`: is in P.

McNaughton, R. (1959). Scheduling with deadlines and loss functions. https://doi.org/10.1287/mnsc.6.1.1
-/
def p54_r0 (R : Reading F) : Prop :=
  InP (R.at p54)

/-- `P2|fixj;pmtn|ΣwjCj`: is strongly NP-hard.

Oguz, C. and Qi, X. (2006). Preemptive scheduling multiprocessor tasks to minimize total weighted completion time on two dedicated processors. None
-/
def p55_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p55)

/-- `R|pmtn|ΣCj`: is strongly NP-hard.

Sitters, R.A. (2001). Two NP-hardness results for preemptive minsum scheduling of unrelated parallel machines. https://doi.org/10.1007/3-540-45535-3_31
-/
def p56_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p56)

/-- `R|pmtn|ΣUj`: is strongly NP-hard.

Sitters, R.A. (2001). Two NP-hardness results for preemptive minsum scheduling of unrelated parallel machines. https://doi.org/10.1007/3-540-45535-3_31
-/
def p57_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p57)

/-- `1|pmtn;rj;pj=p|ΣTj`: is in P.

Tian, Z. and Ng, C.T. and Cheng, T.C.E. (2006). An $O(n^2)$ algorithm for scheduling equal-length preemptive jobs on a single machine to minimize total tardiness. https://doi.org/10.1007/s10951-006-7039-6
-/
def p58_r0 (R : Reading F) : Prop :=
  InP (R.at p58)

/-- `P|pj=1;prec;pmtn|Cmax`: is strongly NP-hard.

Ullman, J.D. (1976). Complexity of sequencing problems. None
-/
def p59_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p59)

/-- `P2|pmtn|ΣwjUj`: is NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p60_r0 (R : Reading F) : Prop :=
  NPHard (R.at p60)

/-- `1|online-rj;pmtn|ΣwjCj`: deterministic competitive ratio ge1.0730.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p61_r0 (R : Reading F) : Prop :=
  DetLowerBound (R.at p61) (1.0730 : ℝ)

/-- `1|online-rj;pmtn|ΣwjCj`: randomized competitive ratio ge1.0389.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p61_r1 (R : Reading F) : Prop :=
  RandLowerBound (R.at p61) (1.0389 : ℝ)

/-- `1|online-rj;pmtn|ΣwjFj`: deterministic competitive ratio ge2.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p62_r0 (R : Reading F) : Prop :=
  DetLowerBound (R.at p62) (2 : ℝ)

/-- `1|online-rj;pmtn|ΣwjFj`: randomized competitive ratio ge4/3.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p62_r1 (R : Reading F) : Prop :=
  RandLowerBound (R.at p62) ((4 : ℝ) / 3)

/-- `P|pmtn;interval order|Cmax`: is in P.

Djellab, Khaled (1999). Scheduling preemptive jobs with precedence constraints on parallel machines. https://doi.org/10.1016/s0377-2217(98)00234-3
-/
def p63_r0 (R : Reading F) : Prop :=
  InP (R.at p63)

/-- `P|pmtn;Am-order|Cmax`: is in P.

Moukrim, Aziz and Quilliot, Alain (2005). Optimal preemptive scheduling on a fixed number of identical parallel machines. https://doi.org/10.1016/j.orl.2004.06.002
-/
def p64_r0 (R : Reading F) : Prop :=
  InP (R.at p64)

/-- `1|rj;prec;pmtn|ΣwjCj`: randomized approximation ratio using alpha-points ≤2+epsilon.

Skutella, Martin (2006). List scheduling in order of $\alpha$-points on a single machine. https://doi.org/10.1007/11671541_9
-/
def p65_r0 (R : Reading F) : Prop :=
  ∀ ε : ℚ, 0 < ε → RandomApprox (R.at p65) (const (2 + ε))

/-- `1|rj;prec;pmtn|ΣwjCj`: has a polynomial-time 2-approximation, by solving a linear program (LP) and doing preemptive list scheduling in order of completion times in the LP solution.

Leslie A. Hall and Andreas S. Schulz and David B. Shmoys and Joel Wein (1997). Scheduling to Minimize Average Completion Time: Off-Line and On-Line Approximation Algorithms. https://doi.org/10.1287/moor.22.3.513
-/
def p65_r1 (R : Reading F) : Prop :=
  Approx (R.at p65) (const (2 : ℝ))

/-- `P|rj;pmtn|ΣwjCj`: has a PTAS.

Afrati, Foto and Bampis, Evripidis and Chekuri, Chandra and Karger, David and Kenyon, Claire and Khanna, Sanjeev and Milis, Ioannis and Queyranne, Maurice and Skutella, Martin and Stein, Clifford and others (1999). Approximation schemes for minimizing average weighted completion time with release dates. https://doi.org/10.1109/sffcs.1999.814574
-/
def p66_r0 (R : Reading F) : Prop :=
  PTAS (R.at p66)

/-- `P|rj;prec;pmtn|ΣwjCj`: has a polynomial-time 3-approximation.

Leslie A. Hall and Andreas S. Schulz and David B. Shmoys and Joel Wein (1997). Scheduling to Minimize Average Completion Time: Off-Line and On-Line Approximation Algorithms. https://doi.org/10.1287/moor.22.3.513
-/
def p67_r0 (R : Reading F) : Prop :=
  Approx (R.at p67) (const (3 : ℝ))

/-- `1|rj;prec;pmtn|ΣFj`: has approximation ratio ge n^frac1(loglog n)^c for some c > 0 under ETH.

Janardhan Kulkarni and Shi Li (2018). Flow-time Optimization for Concurrent Open-Shop and Precedence Constrained Scheduling Models. https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2018.16

Note: the claim is for polynomial-time algorithms.
-/
def p68_r0 (R : Reading F) : Prop :=
  ETH → ∃ c : ℝ, 0 < c ∧ ¬ Approx (R.at p68) (fun x => ((Ops.n p68 x) : ℝ) ^ (1 / Real.log (Real.log (Ops.n p68 x)) ^ c))

/-- `1|rj;pmtn|ΣwjFj`: has a PTAS.

Armbruster, Alexander and Rohwedder, Lars and Wiese, Andreas (2023). A PTAS for Minimizing Weighted Flow Time on a Single Machine. https://doi.org/10.1145/3564246.3585146
-/
def p70_r0 (R : Reading F) : Prop :=
  PTAS (R.at p70)

/-- `1|online-rj;pmtn|ΣUj`: there is a randomized algorithm which is O(1) competitive against an oblivious adversary.

Kalyanasundaram, Bala and Pruhs, Kirk (1998). Maximizing job completions online. https://doi.org/10.1007/3-540-68530-8_20

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p72_r0 (R : Reading F) : Prop :=
  ∃ C : ℝ, RandCompetitiveKept (R.at p72) (Ops.totalW p72) (const C)

/-- `P|online-rj;pmtn|ΣUj`: there is a O(1)-competitive determinstic algorithm.

Moseley, Benjamin and Pruhs, Kirk and Stein, Clifford and Zhou, Rudy (2022). A Competitive Algorithm for Throughput Maximization on Identical Machines. https://doi.org/10.1007/978-3-031-06901-7_30

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p73_r1 (R : Reading F) : Prop :=
  ∃ C : ℝ, DetCompetitiveKept (R.at p73) (Ops.totalW p73) (const C)

/-- `P|pmtn|ΣTj`: is NP-hard.

Kravchenko, Svetlana A. and Werner, Frank (2013). Erratum to: Minimizing total tardiness on parallel machines with preemptions. https://doi.org/10.1007/s10951-013-0313-5
-/
def p74_r0 (R : Reading F) : Prop :=
  NPHard (R.at p74)

end Lax434175.ZooPreemptiveResults
