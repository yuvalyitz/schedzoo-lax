import Lax434175.ZooPreemptiveShops
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, preemptive shop problems
type: definition
---
The 29 results of The Scheduling Zoo on its preemptive shop problems that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooPreemptiveShopsResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters Lax434175.ZooPreemptiveShops

/-- `J|n=k;pmtn|Cmax`, parameter m: is in Ppseudo.

Brucker, P. and Kravchenko, S.A. and Sotskov, Y.N. (1999). Preemptive job-shop scheduling problems with a fixed number of jobs. https://doi.org/10.1007/pl00020906

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p0_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p0) (tplus (lift (Ops.n p0)) (lift (Ops.m p0)))

/-- `J|n=k;pmtn|ΣCj`, parameter m: is in Ppseudo.

Brucker, P. and Kravchenko, S.A. and Sotskov, Y.N. (1999). Preemptive job-shop scheduling problems with a fixed number of jobs. https://doi.org/10.1007/pl00020906

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p1_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p1) (tplus (lift (Ops.n p1)) (lift (Ops.m p1)))

/-- `J2|n=3;pmtn|Cmax`: is NP-hard.

Brucker, P. and Kravchenko, S.A. and Sotskov, Y.N. (1999). Preemptive job-shop scheduling problems with a fixed number of jobs. https://doi.org/10.1007/pl00020906
-/
def p2_r0 (R : Reading F) : Prop :=
  NPHard (R.at p2)

/-- `J2|n=3;pmtn|ΣCj`: is NP-hard.

Brucker, P. and Kravchenko, S.A. and Sotskov, Y.N. (1999). Preemptive job-shop scheduling problems with a fixed number of jobs. https://doi.org/10.1007/pl00020906
-/
def p3_r0 (R : Reading F) : Prop :=
  NPHard (R.at p3)

/-- `O|pmtn;rj|Lmax`: is in P.

Cho, Y. and Sahni, S. (1981). Preemptive scheduling of independent jobs with release and due times on open, flow and job shops. https://doi.org/10.1287/opre.29.3.511
-/
def p4_r0 (R : Reading F) : Prop :=
  InP (R.at p4)

/-- `F2|pmtn|Cmax`: is in P.

Cho, Y. and Sahni, S. (1981). Preemptive scheduling of independent jobs with release and due times on open, flow and job shops. https://doi.org/10.1287/opre.29.3.511
-/
def p5_r0 (R : Reading F) : Prop :=
  InP (R.at p5)

/-- `F2|pmtn|Cmax`: is in P.

Gonzalez, T. and Sahni, S. (1978). Flowshop and jobshop schedules: complexity and approximation. https://doi.org/10.1287/opre.26.1.36
-/
def p5_r1 (R : Reading F) : Prop :=
  InP (R.at p5)

/-- `F2|rj;pmtn|Cmax`: is strongly NP-hard.

Cho, Y. and Sahni, S. (1981). Preemptive scheduling of independent jobs with release and due times on open, flow and job shops. https://doi.org/10.1287/opre.29.3.511
-/
def p6_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p6)

/-- `F2|rj;pmtn|Cmax`: is strongly NP-hard.

Gonzalez, T. and Sahni, S. (1978). Flowshop and jobshop schedules: complexity and approximation. https://doi.org/10.1287/opre.26.1.36
-/
def p6_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p6)

/-- `F3|pmtn|Cmax`: is strongly NP-hard.

Cho, Y. and Sahni, S. (1981). Preemptive scheduling of independent jobs with release and due times on open, flow and job shops. https://doi.org/10.1287/opre.29.3.511
-/
def p7_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p7)

/-- `F3|pmtn|Cmax`: is strongly NP-hard.

Gonzalez, T. and Sahni, S. (1978). Flowshop and jobshop schedules: complexity and approximation. https://doi.org/10.1287/opre.26.1.36
-/
def p7_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p7)

/-- `F2|pmtn|Lmax`: is strongly NP-hard.

Cho, Y. and Sahni, S. (1981). Preemptive scheduling of independent jobs with release and due times on open, flow and job shops. https://doi.org/10.1287/opre.29.3.511
-/
def p8_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p8)

/-- `F2|pmtn|Lmax`: is strongly NP-hard.

Gonzalez, T. and Sahni, S. (1978). Flowshop and jobshop schedules: complexity and approximation. https://doi.org/10.1287/opre.26.1.36
-/
def p8_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p8)

/-- `O2|pmtn|ΣCj`: is NP-hard.

Du, J. and Leung, J.Y.-T. (1993). Minimizing mean flow time in two-machine open shops and flow shops. https://doi.org/10.1006/jagm.1993.1002
-/
def p9_r0 (R : Reading F) : Prop :=
  NPHard (R.at p9)

/-- `F2|pmtn|ΣCj`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. (1993). Minimizing mean flow time in two-machine open shops and flow shops. https://doi.org/10.1006/jagm.1993.1002
-/
def p10_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p10)

/-- `O2|chains;pmtn|Cmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p11_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p11)

/-- `O2|chains;pmtn|ΣCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p12_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p12)

/-- `O2|pmtn|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p13_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p13)

/-- `F2|chains;pmtn|Cmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p14_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p14)

/-- `J2|pmtn|ΣCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p15_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p15)

/-- `O3|pmtn|ΣCj`: is strongly NP-hard.

Liu, C.Y. and Bulfin, R.L. (1985). On the complexity of preemptive open-shop scheduling problems. https://doi.org/10.1016/0167-6377(85)90035-5
-/
def p16_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p16)

/-- `O2|pmtn|ΣUj`: is NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1981). Minimizing maximum lateness in a two-machine open shop. https://doi.org/10.1287/moor.6.1.153
-/
def p17_r0 (R : Reading F) : Prop :=
  NPHard (R.at p17)

/-- `O2|pmtn|ΣUj`: is NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1982). Erratum: ''Minimizing maximum lateness in a two-machine open shop''\ [Math. Oper. Res. \bf 6 (1981), no. 1, 153-158]. https://doi.org/10.1287/moor.6.1.153
-/
def p17_r1 (R : Reading F) : Prop :=
  NPHard (R.at p17)

/-- `J2|pmtn|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1979). Computational complexity of discrete optimization problems. https://doi.org/10.1016/s0167-5060(08)70821-5
-/
def p18_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p18)

/-- `J|prec;rj;n=k;pmtn|ΣwjUj`: is in Ppseudo.

Middendorf, M. and Timkovsky, V.G. (1999). Transversal graphs for partially ordered sets: sequencing, merging and scheduling problems. https://doi.org/10.1023/a:1009827520712

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p19_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p19) (lift (Ops.n p19))

/-- `J|prec;rj;n=k;pmtn|ΣwjTj`: is in Ppseudo.

Middendorf, M. and Timkovsky, V.G. (1999). Transversal graphs for partially ordered sets: sequencing, merging and scheduling problems. https://doi.org/10.1023/a:1009827520712

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p20_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p20) (lift (Ops.n p20))

/-- `J|prec;rj;n=2;pmtn|ΣwjUj`: is in P.

Sotskov, Y.N. (1991). The complexity of shop-scheduling problems with two or three jobs. https://doi.org/10.1016/0377-2217(91)90066-5
-/
def p21_r0 (R : Reading F) : Prop :=
  InP (R.at p21)

/-- `J|prec;rj;n=2;pmtn|ΣwjTj`: is in P.

Sotskov, Y.N. (1991). The complexity of shop-scheduling problems with two or three jobs. https://doi.org/10.1016/0377-2217(91)90066-5
-/
def p22_r0 (R : Reading F) : Prop :=
  InP (R.at p22)

/-- `O2|pmtn;rj|ΣCj`: is strongly NP-hard.

Sriskandarajah, C. and Wagneur, E. (1994). On the complexity of preemptive openshop scheduling problems. https://doi.org/10.1016/0377-2217(94)90406-5
-/
def p23_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p23)

end Lax434175.ZooPreemptiveShopsResults
