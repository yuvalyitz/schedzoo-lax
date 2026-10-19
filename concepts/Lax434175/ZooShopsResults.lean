import Lax434175.ZooShops
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, shop problems
type: definition
---
The 360 results of The Scheduling Zoo on its shop problems that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooShopsResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters Lax434175.ZooShops

/-- `F2|no-idle;no-wait|Cmax`: can be solved in time O(n).

Jean-Charles Billaut and Federico Della Croce and Fabio Salassa and Vincent T'kindt (2017). When Shop Scheduling Meets Dominoes, Eulerian and Hamiltonian Paths. None
-/
def p0_r0 (R : Reading F) : Prop :=
  DecidesWithin (R.at p0) (fun x => (Ops.n p0 x))

/-- `F|no-idle;no-wait|Cmax`: can be solved in polynomial time by a reduction to Eulerian path in directed multi-graphs.

Jean-Charles Billaut and Federico Della Croce and Fabio Salassa and Vincent T'kindt (2017). When Shop Scheduling Meets Dominoes, Eulerian and Hamiltonian Paths. None
-/
def p1_r0 (R : Reading F) : Prop :=
  InP (R.at p1)

/-- `F2|pij=1;tj|Cmax`: is strongly NP-hard.

Yu, W. and Hoogeveen, H. and Lenstra, J.K. (2004). Minimizing makespan in a two-machine flow shop with delays and unit-time operations is NP-hard. https://doi.org/10.1023/b:josh.0000036858.59787.c2
-/
def p3_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p3)

/-- `F2|pij=1;tj|Cmax`: is strongly NP-hard.

Yu, W. (1996). The two-machine flow shop problem with delays and the one-machine total tardiness problem. None
-/
def p3_r2 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p3)

/-- `F||Cmax`: has polynomial time approximation ratio ≥5/4.

Williamson, DP and Hall, LA and Hoogeveen, JA and Hurkens, CAJ and Lenstra, Jan Karel and Sevast'Janov, SV and Shmoys, DB (1997). Short shop schedules. https://doi.org/10.1287/opre.45.2.288

Note: read as holding unless P = NP.
-/
def p4_r1 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p4) ((5 : ℝ) / 4)

/-- `O2||ΣCj`: is strongly NP-hard.

Achugbue, J.O. and Chin, F.Y. (1982). Scheduling the open shop to minimize mean flow time. https://doi.org/10.1137/0211058
-/
def p5_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p5)

/-- `O2|fixj|ΣCj`: is strongly NP-hard.

Achugbue, J.O. and Chin, F.Y. (1982). Scheduling the open shop to minimize mean flow time. https://doi.org/10.1137/0211058
-/
def p6_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p6)

/-- `O2|Mj|ΣCj`: is strongly NP-hard.

Achugbue, J.O. and Chin, F.Y. (1982). Scheduling the open shop to minimize mean flow time. https://doi.org/10.1137/0211058
-/
def p7_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p7)

/-- `F|intree;pij=1|ΣCj`, parameter m: is in P.

Averbakh, I. and Berman, O. and Chernykh, I. (2005). The m-machine flowshop problem with unit-time operations and precedence constraints. None

Note: in P for every fixed value.
-/
def p8_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p8) (lift (Ops.m p8))

/-- `O|pij=1;rj|ΣwjUj`, parameter m: is in P.

Baptiste, P. (2003). On minimizing the weighted number of late jobs in unit execution time open-shops. https://doi.org/10.1016/s0377-2217(02)00759-2

Note: in P for every fixed value.
-/
def p9_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p9) (lift (Ops.m p9))

/-- `J|fixj;n=2|ΣwjUj`: is in P.

Brucker, P. (1995). Scheduling algorithms. None
-/
def p10_r0 (R : Reading F) : Prop :=
  InP (R.at p10)

/-- `J|fixj;n=2|ΣwjTj`: is in P.

Brucker, P. (1995). Scheduling algorithms. None
-/
def p11_r0 (R : Reading F) : Prop :=
  InP (R.at p11)

/-- `F|Mj;prec;rj;n=k|ΣwjUj`, parameter m: is in P.

Brucker, P. (1995). Scheduling algorithms. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p12_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p12) (tplus (lift (Ops.n p12)) (lift (Ops.m p12)))

/-- `F|Mj;prec;rj;n=k|ΣwjTj`, parameter m: is in P.

Brucker, P. (1995). Scheduling algorithms. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p13_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p13) (tplus (lift (Ops.n p13)) (lift (Ops.m p13)))

/-- `O|Mj;prec;rj;n=k|ΣwjUj`, parameter m: is in P.

Brucker, P. (1995). Scheduling algorithms. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p14_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p14) (tplus (lift (Ops.n p14)) (lift (Ops.m p14)))

/-- `O|Mj;prec;rj;n=k|ΣwjTj`, parameter m: is in P.

Brucker, P. (1995). Scheduling algorithms. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p15_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p15) (tplus (lift (Ops.n p15)) (lift (Ops.m p15)))

/-- `O|pij=1;intree|Lmax`: is in P.

Brucker, P. (1995). Scheduling algorithms. None
-/
def p16_r0 (R : Reading F) : Prop :=
  InP (R.at p16)

/-- `O|pij=1;intree|Lmax`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p16_r1 (R : Reading F) : Prop :=
  InP (R.at p16)

/-- `O2|pij=1;prec;rj|Lmax`: is in P.

Brucker, P. (1995). Scheduling algorithms. None
-/
def p17_r0 (R : Reading F) : Prop :=
  InP (R.at p17)

/-- `O2|pij=1;prec;rj|Lmax`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p17_r1 (R : Reading F) : Prop :=
  InP (R.at p17)

/-- `J|prec;rj;n=k;no-wait|ΣwjUj`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p18_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p18) (lift (Ops.n p18))

/-- `J|prec;rj;n=k;no-wait|ΣwjTj`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p19_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p19) (lift (Ops.n p19))

/-- `O|pij=1;chains;rj|Lmax`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p20_r0 (R : Reading F) : Prop :=
  InP (R.at p20)

/-- `O|pij=1;intree;no-wait|ΣCj`, parameter m: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None

Note: in P for every fixed value.
-/
def p21_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p21) (lift (Ops.m p21))

/-- `O|pij=1;rj;no-wait|ΣwjUj`, parameter m: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None

Note: in P for every fixed value.
-/
def p22_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p22) (lift (Ops.m p22))

/-- `F3;R1|pij=1;tk;rj|Cmax`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p23_r0 (R : Reading F) : Prop :=
  InP (R.at p23)

/-- `F3;R1|pij=1;tk|Lmax`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p24_r0 (R : Reading F) : Prop :=
  InP (R.at p24)

/-- `F|pij=1;tj|ΣCj`: is in P.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p25_r0 (R : Reading F) : Prop :=
  InP (R.at p25)

/-- `F2|pij=1;tj;rj|ΣCj`: is strongly NP-hard.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p26_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p26)

/-- `F2|pij=1;tj|ΣwjCj`: is strongly NP-hard.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p27_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p27)

/-- `O2|pij=1;tjkl=T;rj|Cmax`: is in P.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p28_r0 (R : Reading F) : Prop :=
  InP (R.at p28)

/-- `O2|pij=1;tkl|Cmax`: is in P.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p29_r0 (R : Reading F) : Prop :=
  InP (R.at p29)

/-- `O2|pij=1;tkl|Cmax`: is in P.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p29_r1 (R : Reading F) : Prop :=
  InP (R.at p29)

/-- `O2|pij=1;tkl|ΣwjCj`: is in P.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p30_r0 (R : Reading F) : Prop :=
  InP (R.at p30)

/-- `O2|pij=1;tjkl=T|ΣUj`: is in P.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p31_r0 (R : Reading F) : Prop :=
  InP (R.at p31)

/-- `O2|pij=1;tj;rj|ΣCj`: is strongly NP-hard.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p32_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p32)

/-- `O2|pij=1;tj|ΣwjCj`: is strongly NP-hard.

Brucker, P. and Cheng, T.C.E. and Knust, S. and Shakhlevich, N.V. (2004). Complexity results for flow-shop and open-shop problems with transportation delays. https://doi.org/10.1023/b:anor.0000030683.64615.c8
-/
def p33_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p33)

/-- `O|pij=1;intree;no-wait|Lmax`: is in P.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p34_r0 (R : Reading F) : Prop :=
  InP (R.at p34)

/-- `O|pij=1;intree;no-wait|Lmax`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p34_r1 (R : Reading F) : Prop :=
  InP (R.at p34)

/-- `O|pij=1;outtree;no-wait|Lmax`: is strongly NP-hard.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p35_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p35)

/-- `F|Mj;intree;rj;pij=1|Cmax`: is strongly NP-hard.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p36_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p36)

/-- `F|Mj;outtree;pij=1|Lmax`: is strongly NP-hard.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p37_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p37)

/-- `O|pij=1;rj|Lmax`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p38_r0 (R : Reading F) : Prop :=
  InP (R.at p38)

/-- `O|pij=1;rj|Lmax`: is in P.

unknown author (unknown year). see: Network Flow Problem. None
-/
def p38_r1 (R : Reading F) : Prop :=
  InP (R.at p38)

/-- `O|pij=1|ΣwjCj`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p39_r0 (R : Reading F) : Prop :=
  InP (R.at p39)

/-- `O2|pij=1;prec|ΣUj`: is strongly NP-hard.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p40_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p40)

/-- `O|pij=1;tree;no-wait|Cmax`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p41_r0 (R : Reading F) : Prop :=
  InP (R.at p41)

/-- `O|pij=1;tree;no-wait|Cmax`: is in P.

Hu, T.C. (1961). Parallel sequencing and assembly line problems. https://doi.org/10.1287/opre.9.6.841
-/
def p41_r1 (R : Reading F) : Prop :=
  InP (R.at p41)

/-- `O2|pij=1;prec;no-wait|Cmax`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p42_r0 (R : Reading F) : Prop :=
  InP (R.at p42)

/-- `O2|pij=1;prec;no-wait|Cmax`: is in P.

Coffman, Jr., E.G. and Graham, R.L. (1971/1972). Optimal scheduling for two-processor systems. https://doi.org/10.1007/bf00288685
-/
def p42_r1 (R : Reading F) : Prop :=
  InP (R.at p42)

/-- `O|pij=1;rj;no-wait|Lmax`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p43_r0 (R : Reading F) : Prop :=
  InP (R.at p43)

/-- `O|pij=1;rj;no-wait|Lmax`: is in P.

Simons, B. (1983). Multiprocessor scheduling of unit-time jobs with arbitrary release times and deadlines. https://doi.org/10.1137/0212018
-/
def p43_r1 (R : Reading F) : Prop :=
  InP (R.at p43)

/-- `O|pij=1;outtree;no-wait|ΣCj`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p44_r0 (R : Reading F) : Prop :=
  InP (R.at p44)

/-- `O|pij=1;outtree;no-wait|ΣCj`: is in P.

Hu, T.C. (1961). Parallel sequencing and assembly line problems. https://doi.org/10.1287/opre.9.6.841
-/
def p44_r1 (R : Reading F) : Prop :=
  InP (R.at p44)

/-- `O|pij=1;no-wait|ΣwjTj`: is in P.

Brucker, P. and Jurisch, B. and Jurisch, M. (1993). Open shop problems with unit time operations. https://doi.org/10.1007/bf01415528
-/
def p45_r0 (R : Reading F) : Prop :=
  InP (R.at p45)

/-- `F|Mj;n=3|Cmax`: is NP-hard.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030
-/
def p46_r0 (R : Reading F) : Prop :=
  NPHard (R.at p46)

/-- `F|Mj;rj;pij=1|Cmax`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p47_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p47) (lift (Ops.m p47))

/-- `F|Mj;rj;pij=1|ΣCj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p48_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p48) (lift (Ops.m p48))

/-- `F|Mj;pij=1|ΣwjCj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p49_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p49) (lift (Ops.m p49))

/-- `F|Mj;pij=1|ΣwjUj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p50_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p50) (lift (Ops.m p50))

/-- `F|Mj;pij=1|ΣTj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p51_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p51) (lift (Ops.m p51))

/-- `J|Mj;prec;rj;pij=1;n=k|ΣwjUj`: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p52_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p52) (lift (Ops.n p52))

/-- `J|Mj;prec;rj;pij=1;n=k|ΣwjTj`: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p53_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p53) (lift (Ops.n p53))

/-- `O|Mj;rj;pij=1|Cmax`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p54_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p54) (lift (Ops.m p54))

/-- `O|Mj;rj;pij=1|ΣCj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p55_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p55) (lift (Ops.m p55))

/-- `O|Mj;pij=1|ΣwjCj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p56_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p56) (lift (Ops.m p56))

/-- `O|Mj;pij=1|ΣwjUj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p57_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p57) (lift (Ops.m p57))

/-- `O|Mj;pij=1|ΣTj`, parameter m: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030

Note: in P for every fixed value.
-/
def p58_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p58) (lift (Ops.m p58))

/-- `F|pij=1;outtree;rj|Cmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p59_r0 (R : Reading F) : Prop :=
  InP (R.at p59)

/-- `F|pij=1;tree|Cmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p60_r0 (R : Reading F) : Prop :=
  InP (R.at p60)

/-- `F|pij=1;intree|Lmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p61_r0 (R : Reading F) : Prop :=
  InP (R.at p61)

/-- `F2|pij=1;prec;rj|Lmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p62_r0 (R : Reading F) : Prop :=
  InP (R.at p62)

/-- `O2|fixj|Cmax`: is in P.

Brucker, P. and Krämer, A. (1995). Shop scheduling problems with multiprocessor tasks on dedicated processors. https://doi.org/10.1007/bf02099688
-/
def p63_r0 (R : Reading F) : Prop :=
  InP (R.at p63)

/-- `J2|fixj;n=k|Cmax`: is in P.

Brucker, P. and Krämer, A. (1995). Shop scheduling problems with multiprocessor tasks on dedicated processors. https://doi.org/10.1007/bf02099688

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p64_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p64) (lift (Ops.n p64))

/-- `J2|fixj;n=k|Cmax`: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p64_r1 (R : Reading F) : Prop :=
  InPFixed (R.at p64) (lift (Ops.n p64))

/-- `F2|fixj|Cmax`: is strongly NP-hard.

Brucker, P. and Krämer, A. (1995). Shop scheduling problems with multiprocessor tasks on dedicated processors. https://doi.org/10.1007/bf02099688
-/
def p65_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p65)

/-- `J2|fixj;pij=1|Cmax`: is strongly NP-hard.

Brucker, P. and Krämer, A. (1995). Shop scheduling problems with multiprocessor tasks on dedicated processors. https://doi.org/10.1007/bf02099688
-/
def p66_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p66)

/-- `J|prec;pij=1;rj;n=k|ΣwjUj`: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p67_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p67) (lift (Ops.n p67))

/-- `J|prec;pij=1;rj;n=k|ΣwjTj`: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p68_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p68) (lift (Ops.n p68))

/-- `F|fixj;rj;pij=1|Cmax`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p69_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p69) (lift (Ops.m p69))

/-- `F|fixj;rj;pij=1|ΣCj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p70_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p70) (lift (Ops.m p70))

/-- `F|fixj;pij=1|ΣwjCj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p71_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p71) (lift (Ops.m p71))

/-- `F|fixj;pij=1|ΣwjUj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p72_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p72) (lift (Ops.m p72))

/-- `F|fixj;pij=1|ΣwjTj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p73_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p73) (lift (Ops.m p73))

/-- `J|fixj;prec;rj;pij=1;n=k|ΣwjUj`: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p74_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p74) (lift (Ops.n p74))

/-- `J|fixj;prec;rj;pij=1;n=k|ΣwjTj`: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p75_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p75) (lift (Ops.n p75))

/-- `O|fixj;rj;pij=1|Cmax`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p76_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p76) (lift (Ops.m p76))

/-- `O|fixj;rj;pij=1|ΣCj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p77_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p77) (lift (Ops.m p77))

/-- `O|fixj;pij=1|ΣwjCj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p78_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p78) (lift (Ops.m p78))

/-- `O|fixj;pij=1|ΣwjUj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p79_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p79) (lift (Ops.m p79))

/-- `O|fixj;pij=1|ΣTj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p80_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p80) (lift (Ops.m p80))

/-- `F|pij=1;outtree;rj|ΣCj`: is in P.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p81_r0 (R : Reading F) : Prop :=
  InP (R.at p81)

/-- `F2|pij=1;prec|ΣCj`: is in P.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p82_r0 (R : Reading F) : Prop :=
  InP (R.at p82)

/-- `F|pij=1;intree;rj|Cmax`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p83_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p83)

/-- `F|pij=1;outtree|Lmax`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p84_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p84)

/-- `F2|pij=1;chains|ΣUj`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p85_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p85)

/-- `F3|pij=1;chains|ΣUj`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p86_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p86)

/-- `F2|pij=1;chains|ΣTj`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p87_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p87)

/-- `F3|pij=1;chains|ΣTj`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p88_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p88)

/-- `F|fixj;tree;rj;pij=1|Cmax`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p89_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p89)

/-- `F|fixj;tree;pij=1|Lmax`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p90_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p90)

/-- `O|pij=1;rj|ΣCj`: is in P.

Brucker, P. and Kravchenko, S.A. (2004). Complexity of mean flow time scheduling problems with release dates. None
-/
def p91_r0 (R : Reading F) : Prop :=
  InP (R.at p91)

/-- `O|pij=1;rj|ΣCj`, parameter m: is in P.

Tautenhahn, T. and Woeginger, G.J. (1997). Minimizing the total completion time in a unit-time open shop with release times. https://doi.org/10.1016/s0167-6377(97)00015-1

Note: in P for every fixed value.
-/
def p91_r1 (R : Reading F) : Prop :=
  InPFixed (R.at p91) (lift (Ops.m p91))

/-- `J2|n=k|ΣwjUj`: is in P.

Brucker, P. and Kravchenko, S.A. and Sotskov, Y.N. (1997). On the complexity of two machine job-shop scheduling with regular objective functions. https://doi.org/10.1007/s002910050013

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p92_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p92) (lift (Ops.n p92))

/-- `J2|n=k|ΣwjTj`: is in P.

Brucker, P. and Kravchenko, S.A. and Sotskov, Y.N. (1997). On the complexity of two machine job-shop scheduling with regular objective functions. https://doi.org/10.1007/s002910050013

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p93_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p93) (lift (Ops.n p93))

/-- `F2;S1|pij=p;sij=s;rj|Cmax`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p94_r0 (R : Reading F) : Prop :=
  InP (R.at p94)

/-- `F;S1|pij=1;sij=s;rj|Cmax`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p95_r0 (R : Reading F) : Prop :=
  InP (R.at p95)

/-- `F;S1|pij=p;sij=s|Cmax`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p96_r0 (R : Reading F) : Prop :=
  InP (R.at p96)

/-- `F2;S1|pij=p;sij=s;rj|ΣCj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p97_r0 (R : Reading F) : Prop :=
  InP (R.at p97)

/-- `F;S1|pij=1;sij=s;rj|ΣCj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p98_r0 (R : Reading F) : Prop :=
  InP (R.at p98)

/-- `F2;S1|pij=p|Cmax`: is NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p99_r0 (R : Reading F) : Prop :=
  NPHard (R.at p99)

/-- `F2;S1|sij=s|Cmax`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p100_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p100)

/-- `F2;S1|pij=1;rj|Lmax`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p101_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p101)

/-- `F3;S1|pij=1;rj|Lmax`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p102_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p102)

/-- `F2;S1|pij=1;rj|ΣCj`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p103_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p103)

/-- `F3;S1|pij=1;rj|ΣCj`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p104_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p104)

/-- `F2;S1|pij=1|ΣwjUj`: is NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p105_r0 (R : Reading F) : Prop :=
  NPHard (R.at p105)

/-- `F3;S1|pij=1|ΣwjUj`: is NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p106_r0 (R : Reading F) : Prop :=
  NPHard (R.at p106)

/-- `F2;S1|pij=1|ΣTj`: is NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p107_r0 (R : Reading F) : Prop :=
  NPHard (R.at p107)

/-- `F3;S1|pij=1|ΣTj`: is NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p108_r0 (R : Reading F) : Prop :=
  NPHard (R.at p108)

/-- `F2;S1|pij=1|ΣwjTj`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p109_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p109)

/-- `F3;S1|pij=1|ΣwjTj`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p110_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p110)

/-- `F3;S1|sij=1|Cmax`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p111_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p111)

/-- `F2;S1|sij=1|ΣCj`: is strongly NP-hard.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p112_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p112)

/-- `F2;S1|pij=p;sij=s|ΣwjUj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p113_r0 (R : Reading F) : Prop :=
  InP (R.at p113)

/-- `F;S1|pij=1;sij=s|ΣwjUj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p114_r0 (R : Reading F) : Prop :=
  InP (R.at p114)

/-- `F2;S1|pij=p;sij=s|ΣwjTj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p115_r0 (R : Reading F) : Prop :=
  InP (R.at p115)

/-- `F;S1|pij=1;sij=s|ΣwjTj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p116_r0 (R : Reading F) : Prop :=
  InP (R.at p116)

/-- `F2;S1|pij=p;sij=1;rj|ΣwjCj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p117_r0 (R : Reading F) : Prop :=
  InP (R.at p117)

/-- `F2;S1|pij=p;sij=1;rj|ΣwjUj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p118_r0 (R : Reading F) : Prop :=
  InP (R.at p118)

/-- `F2;S1|pij=p;sij=1;rj|ΣTj`: is in P.

Brucker, P. and Knust, S. and Wang, G. (2005). Complexity results for flow-shop problems with a single server. https://doi.org/10.1016/j.ejor.2004.04.010
-/
def p119_r0 (R : Reading F) : Prop :=
  InP (R.at p119)

/-- `O|pij=1;tree|Cmax`: is in P.

Bräsel, H. and Kluge, D. and Werner, F. (1994). A polynomial algorithm for the $[n/m/0,\ t\sbij=1, tree/C\sb\max]$ open shop problem. None
-/
def p120_r0 (R : Reading F) : Prop :=
  InP (R.at p120)

/-- `O|pij=1;outtree|ΣCj`: is in P.

Bräsel, H. and Kluge, D. and Werner, F. (1995). A polynomial algorithm for an open shop problem with unit processing times and tree constraints. https://doi.org/10.1016/0166-218x(93)e0156-s
-/
def p121_r0 (R : Reading F) : Prop :=
  InP (R.at p121)

/-- `O2|pij=1;tree|ΣCj`: is in P.

Bräsel, H. and Kluge, D. and Werner, F. (1995). A polynomial algorithm for an open shop problem with unit processing times and tree constraints. https://doi.org/10.1016/0166-218x(93)e0156-s
-/
def p122_r0 (R : Reading F) : Prop :=
  InP (R.at p122)

/-- `F2|pij=1;prec;rj|ΣCj`: is in P.

Baptiste, P. and Timkovsky, V. (2004). Shortest path to nonpreemptive schedules of unit-time jobs on two identical parallel machines with minimum total completion time. https://doi.org/10.1007/s001860300336
-/
def p123_r0 (R : Reading F) : Prop :=
  InP (R.at p123)

/-- `O2|pij=1;prec|ΣCj`: is in P.

Coffman, Jr., E.G. and Sethuraman, J. and Timkovsky, V.G. (2003). Ideal preemptive schedules on two processors. https://doi.org/10.1007/s00236-003-0119-6
-/
def p124_r0 (R : Reading F) : Prop :=
  InP (R.at p124)

/-- `F2|no-wait|Cmax`: is in P.

Gilmore, P.C. and Gomory, R.E. (1964). Sequencing a one state-variable machine: A solvable case of the traveling salesman problem. https://doi.org/10.1287/opre.12.5.655
-/
def p125_r0 (R : Reading F) : Prop :=
  InP (R.at p125)

/-- `F2|no-wait|Cmax`: is in P.

Reddi, S.S. and Ramamoorthy, C.V. (1972). On the flow-shop sequencing problem with no wait in process. https://doi.org/10.2307/3007887
-/
def p125_r1 (R : Reading F) : Prop :=
  InP (R.at p125)

/-- `F3||Cmax`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. and Sethi, R. (1976). The complexity of flowshop and jobshop scheduling. https://doi.org/10.1287/moor.1.2.117
-/
def p126_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p126)

/-- `F2||ΣCj`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. and Sethi, R. (1976). The complexity of flowshop and jobshop scheduling. https://doi.org/10.1287/moor.1.2.117
-/
def p127_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p127)

/-- `J2||ΣCj`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. and Sethi, R. (1976). The complexity of flowshop and jobshop scheduling. https://doi.org/10.1287/moor.1.2.117
-/
def p128_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p128)

/-- `F2|fixj|ΣCj`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. and Sethi, R. (1976). The complexity of flowshop and jobshop scheduling. https://doi.org/10.1287/moor.1.2.117
-/
def p129_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p129)

/-- `F3|Mj|Cmax`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. and Sethi, R. (1976). The complexity of flowshop and jobshop scheduling. https://doi.org/10.1287/moor.1.2.117
-/
def p130_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p130)

/-- `F2|Mj|ΣCj`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. and Sethi, R. (1976). The complexity of flowshop and jobshop scheduling. https://doi.org/10.1287/moor.1.2.117
-/
def p131_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p131)

/-- `O2||Cmax`: is in P.

Gonzalez, T. and Sahni, S. (1976). Open shop scheduling to minimize finish time. https://doi.org/10.1145/321978.321985
-/
def p132_r0 (R : Reading F) : Prop :=
  InP (R.at p132)

/-- `O3||Cmax`: is NP-hard.

Gonzalez, T. and Sahni, S. (1976). Open shop scheduling to minimize finish time. https://doi.org/10.1145/321978.321985
-/
def p133_r0 (R : Reading F) : Prop :=
  NPHard (R.at p133)

/-- `O|fixj;n=3|Cmax`: is NP-hard.

Gonzalez, T. and Sahni, S. (1976). Open shop scheduling to minimize finish time. https://doi.org/10.1145/321978.321985
-/
def p134_r0 (R : Reading F) : Prop :=
  NPHard (R.at p134)

/-- `O3|fixj|Cmax`: is NP-hard.

Gonzalez, T. and Sahni, S. (1976). Open shop scheduling to minimize finish time. https://doi.org/10.1145/321978.321985
-/
def p135_r0 (R : Reading F) : Prop :=
  NPHard (R.at p135)

/-- `O|Mj;n=3|Cmax`: is NP-hard.

Gonzalez, T. and Sahni, S. (1976). Open shop scheduling to minimize finish time. https://doi.org/10.1145/321978.321985
-/
def p136_r0 (R : Reading F) : Prop :=
  NPHard (R.at p136)

/-- `O3|Mj|Cmax`: is NP-hard.

Gonzalez, T. and Sahni, S. (1976). Open shop scheduling to minimize finish time. https://doi.org/10.1145/321978.321985
-/
def p137_r0 (R : Reading F) : Prop :=
  NPHard (R.at p137)

/-- `F2;R1|pij=1;tjk|Cmax`: is in P.

Hurink, J. and Knust, S. (2001). Flow-shop problems with transportation times and a single robot. https://doi.org/10.1016/s0166-218x(00)00316-4
-/
def p138_r0 (R : Reading F) : Prop :=
  InP (R.at p138)

/-- `F2;R1|pij=p;tj∈T1,T2|Cmax`: is in P.

Hurink, J. and Knust, S. (2001). Flow-shop problems with transportation times and a single robot. https://doi.org/10.1016/s0166-218x(00)00316-4
-/
def p139_r0 (R : Reading F) : Prop :=
  InP (R.at p139)

/-- `F;R1|n≥m-1;pij=p;tk|Cmax`: is in P.

Hurink, J. and Knust, S. (2001). Flow-shop problems with transportation times and a single robot. https://doi.org/10.1016/s0166-218x(00)00316-4
-/
def p140_r0 (R : Reading F) : Prop :=
  InP (R.at p140)

/-- `F2;R1|pij=p;tj|Cmax`: is strongly NP-hard.

Hurink, J. and Knust, S. (2001). Flow-shop problems with transportation times and a single robot. https://doi.org/10.1016/s0166-218x(00)00316-4
-/
def p141_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p141)

/-- `F2;R1|tjk=T|Cmax`: is strongly NP-hard.

Hurink, J. and Knust, S. (2001). Flow-shop problems with transportation times and a single robot. https://doi.org/10.1016/s0166-218x(00)00316-4
-/
def p142_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p142)

/-- `F2;R1|tjk=T|Cmax`: is NP-hard.

Kise, H. (1991). On an automated two-machine flowshop scheduling problem with infinite buffer. https://doi.org/10.15807/jorsj.34.354
-/
def p142_r1 (R : Reading F) : Prop :=
  NPHard (R.at p142)

/-- `F2||Cmax`: is in P.

Johnson, S.M. (1954). Optimal Two-and-Three-Stage Production Schedules with Set-up Times included. None
-/
def p143_r0 (R : Reading F) : Prop :=
  InP (R.at p143)

/-- `F2|tk|Cmax`: is in P.

Johnson, S.M. (1954). Optimal Two-and-Three-Stage Production Schedules with Set-up Times included. None
-/
def p144_r0 (R : Reading F) : Prop :=
  InP (R.at p144)

/-- `F2|tjk=T|Cmax`: is in P.

Johnson, S.M. (1954). Optimal Two-and-Three-Stage Production Schedules with Set-up Times included. None
-/
def p145_r0 (R : Reading F) : Prop :=
  InP (R.at p145)

/-- `J|Mj;prec;rj;n=2|Lmax`: is in P.

Jurisch, B. (1995). Lower bounds for the job-shop scheduling problem on multi-purpose machines. https://doi.org/10.1016/0166-218x(93)e0124-h
-/
def p146_r0 (R : Reading F) : Prop :=
  InP (R.at p146)

/-- `J2|Mj;n=3|Cmax`: is in Ppseudo.

Jurisch, B. (1995). Lower bounds for the job-shop scheduling problem on multi-purpose machines. https://doi.org/10.1016/0166-218x(93)e0124-h
-/
def p147_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p147)

/-- `J2|Mj;n=3|Cmax`: is NP-hard.

Jurisch, B. (1995). Lower bounds for the job-shop scheduling problem on multi-purpose machines. https://doi.org/10.1016/0166-218x(93)e0124-h
-/
def p147_r1 (R : Reading F) : Prop :=
  NPHard (R.at p147)

/-- `J2|Mj;n=3|Cmax`: is in Ppseudo.

Meyer, W. (1992). Geometrische Methoden zur L\"osung von Job-Shop Problemen und deren Verallgemeinerungen. None
-/
def p147_r2 (R : Reading F) : Prop :=
  PseudoPoly (R.at p147)

/-- `J2|Mj;n=3|Cmax`: is NP-hard.

Meyer, W. (1992). Geometrische Methoden zur L\"osung von Job-Shop Problemen und deren Verallgemeinerungen. None
-/
def p147_r3 (R : Reading F) : Prop :=
  NPHard (R.at p147)

/-- `O|Mj;pij=1|Cmax`: is in Ppseudo.

Jurisch, B. (1995). Lower bounds for the job-shop scheduling problem on multi-purpose machines. https://doi.org/10.1016/0166-218x(93)e0124-h
-/
def p148_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p148)

/-- `J2|pij=1;no-wait|Cmax`: is in Ppseudo.

Kubiak, W. (1989). A pseudo-polynomial algorithm for a two-machine no-wait job-shop scheduling problem. https://doi.org/10.1016/0377-2217(89)90225-7
-/
def p149_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p149)

/-- `J2|pij=1;no-wait|Cmax`: is NP-hard.

Timkovsky, V.G. (1985). On the complexity of scheduling an arbitrary system. None
-/
def p149_r1 (R : Reading F) : Prop :=
  NPHard (R.at p149)

/-- `F|fixj;prec;rj;n=k|ΣwjUj`, parameter m: is in P.

Krämer, A. (1995). Scheduling multiprocessortasks on dedicated processors. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p150_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p150) (tplus (lift (Ops.n p150)) (lift (Ops.m p150)))

/-- `F|fixj;prec;rj;n=k|ΣwjTj`, parameter m: is in P.

Krämer, A. (1995). Scheduling multiprocessortasks on dedicated processors. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p151_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p151) (tplus (lift (Ops.n p151)) (lift (Ops.m p151)))

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjUj`: is in P.

Krämer, A. (1995). Scheduling multiprocessortasks on dedicated processors. None
-/
def p152_r0 (R : Reading F) : Prop :=
  InP (R.at p152)

/-- `O|fixj;prec;rj;n=k|ΣwjUj`, parameter m: is in P.

Krämer, A. (1995). Scheduling multiprocessortasks on dedicated processors. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p153_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p153) (tplus (lift (Ops.n p153)) (lift (Ops.m p153)))

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjTj`: is in P.

Krämer, A. (1995). Scheduling multiprocessortasks on dedicated processors. None
-/
def p154_r0 (R : Reading F) : Prop :=
  InP (R.at p154)

/-- `O|fixj;prec;rj;n=k|ΣwjTj`, parameter m: is in P.

Krämer, A. (1995). Scheduling multiprocessortasks on dedicated processors. None

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs and of m.
-/
def p155_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p155) (tplus (lift (Ops.n p155)) (lift (Ops.m p155)))

/-- `F|fixj;n=3|Cmax`: is NP-hard.

Krämer, A. (1995). Scheduling multiprocessortasks on dedicated processors. None
-/
def p156_r0 (R : Reading F) : Prop :=
  NPHard (R.at p156)

/-- `F2;R1|pij=p;tk;rj|ΣwjCj`: is in P.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p157_r0 (R : Reading F) : Prop :=
  InP (R.at p157)

/-- `F2;R1|pij=p;tk;rj|ΣwjUj`: is in P.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p158_r0 (R : Reading F) : Prop :=
  InP (R.at p158)

/-- `F2;R1|pij=p;tk;rj|ΣTj`: is in P.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p159_r0 (R : Reading F) : Prop :=
  InP (R.at p159)

/-- `F2;R1|pij=p;tk|ΣwjTj`: is in P.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p160_r0 (R : Reading F) : Prop :=
  InP (R.at p160)

/-- `F3;R1|pij=p;tjk;rj|Cmax`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p161_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p161)

/-- `F2;R1|pij=1;tj;rj|Lmax`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p162_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p162)

/-- `F3;R1|pij=1;tjk;rj|Lmax`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p163_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p163)

/-- `F3;R1|pij=p;tjk|Lmax`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p164_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p164)

/-- `F2;R1|pij=1;tj;rj|ΣCj`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p165_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p165)

/-- `F3;R1|pij=1;tjk;rj|ΣCj`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p166_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p166)

/-- `F2;R1|pij=1;tj|ΣwjUj`: is NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p167_r0 (R : Reading F) : Prop :=
  NPHard (R.at p167)

/-- `F3;R1|pij=1;tjk|ΣwjUj`: is NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p168_r0 (R : Reading F) : Prop :=
  NPHard (R.at p168)

/-- `F2;R1|pij=1;tj|ΣTj`: is NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p169_r0 (R : Reading F) : Prop :=
  NPHard (R.at p169)

/-- `F3;R1|pij=1;tjk|ΣTj`: is NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p170_r0 (R : Reading F) : Prop :=
  NPHard (R.at p170)

/-- `F2;R1|pij=1;tj|ΣwjTj`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p171_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p171)

/-- `F3;R1|pij=1;tjk|ΣwjTj`: is strongly NP-hard.

Knust, S. (1999). Shop-scheduling problems with transportation. None
-/
def p172_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p172)

/-- `J2|pij=1|ΣUj`: is in P.

Kravchenko, S.A. (1999). Minimizing the number of late jobs for the two-machine unit-time job-shop scheduling problem. https://doi.org/10.1016/s0166-218x(99)00165-1
-/
def p173_r0 (R : Reading F) : Prop :=
  InP (R.at p173)

/-- `J2|pij=1|ΣwjUj`: is in Ppseudo.

Kravchenko, S.A. (1999). Minimizing the number of late jobs for the two-machine unit-time job-shop scheduling problem. https://doi.org/10.1016/s0166-218x(99)00165-1
-/
def p174_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p174)

/-- `J2|pij=1|ΣwjUj`: is NP-hard.

Kravchenko, S.A. (1999). Minimizing the number of late jobs for the two-machine unit-time job-shop scheduling problem. https://doi.org/10.1016/s0166-218x(99)00165-1
-/
def p174_r1 (R : Reading F) : Prop :=
  NPHard (R.at p174)

/-- `J2|Mj;pij=1|ΣwjUj`: is NP-hard.

Kravchenko, S.A. (1999). Minimizing the number of late jobs for the two-machine unit-time job-shop scheduling problem. https://doi.org/10.1016/s0166-218x(99)00165-1
-/
def p175_r0 (R : Reading F) : Prop :=
  NPHard (R.at p175)

/-- `O|pij=1;no-wait|ΣwjUj`: is in P.

Kubiak, W. and Sriskandarajah, C. and Zaras, K. (1991). A note on the complexity of openshop scheduling problems. https://doi.org/10.1080/03155986.1991.11732176
-/
def p176_r0 (R : Reading F) : Prop :=
  InP (R.at p176)

/-- `O2|no-wait|ΣCj`: is strongly NP-hard.

Kubiak, W. and Sriskandarajah, C. and Zaras, K. (1991). A note on the complexity of openshop scheduling problems. https://doi.org/10.1080/03155986.1991.11732176
-/
def p177_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p177)

/-- `J2|pij=1|ΣCj`: is in P.

Kubiak, W. and Timkovsky, V.G. (1996). A polynomial-time algorithm for total completion time minimization in two-machine job-shop with unit-time operations. None
-/
def p178_r0 (R : Reading F) : Prop :=
  InP (R.at p178)

/-- `J2|pij=1;no-wait|ΣCj`: is in P.

Kravchenko, S.A. (1998). A polynomial algorithm for a two-machine no-wait job-shop scheduling problem. https://doi.org/10.1016/s0377-2217(97)00102-1
-/
def p179_r0 (R : Reading F) : Prop :=
  InP (R.at p179)

/-- `O|pij=1;rj|ΣUj`: is strongly NP-hard.

Kravchenko, S.A. (1999). On the complexity of minimizing the number of late jobs in unit time open shops. https://doi.org/10.1016/s0166-218x(99)00202-4
-/
def p180_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p180)

/-- `O|fixj;rj;pij=1|ΣUj`: is strongly NP-hard.

Kravchenko, S.A. (1999). On the complexity of minimizing the number of late jobs in unit time open shops. https://doi.org/10.1016/s0166-218x(99)00202-4
-/
def p181_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p181)

/-- `O|Mj;rj;pij=1|ΣUj`: is strongly NP-hard.

Kravchenko, S.A. (1999). On the complexity of minimizing the number of late jobs in unit time open shops. https://doi.org/10.1016/s0166-218x(99)00202-4
-/
def p182_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p182)

/-- `O||Cmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p183_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p183)

/-- `O||Cmax`: has polynomial time approximation ratio ≥5/4.

Williamson, DP and Hall, LA and Hoogeveen, JA and Hurkens, CAJ and Lenstra, Jan Karel and Sevast'Janov, SV and Shmoys, DB (1997). Short shop schedules. https://doi.org/10.1287/opre.45.2.288

Note: read as holding unless P = NP.
-/
def p183_r1 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p183) ((5 : ℝ) / 4)

/-- `O2|pij=1;intree|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p184_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p184)

/-- `O2|pij=1;outtree|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p185_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p185)

/-- `J3|pij=1|ΣCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p186_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p186)

/-- `J3|fixj;pij=1|ΣCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p187_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p187)

/-- `O|fixj|Cmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p188_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p188)

/-- `J3|Mj;pij=1|ΣCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p189_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p189)

/-- `O|Mj|Cmax`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p190_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p190)

/-- `O|pij=1|ΣUj`: is in P.

Liu, C.Y. and Bulfin, R.L. (1988). Scheduling open shops with unit execution times to minimize functions of due dates. https://doi.org/10.1287/opre.36.4.553
-/
def p191_r0 (R : Reading F) : Prop :=
  InP (R.at p191)

/-- `O|pij=1|ΣTj`: is in P.

Liu, C.Y. and Bulfin, R.L. (1988). Scheduling open shops with unit execution times to minimize functions of due dates. https://doi.org/10.1287/opre.36.4.553
-/
def p192_r0 (R : Reading F) : Prop :=
  InP (R.at p192)

/-- `O2|rj|Cmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1981). Minimizing maximum lateness in a two-machine open shop. https://doi.org/10.1287/moor.6.1.153
-/
def p193_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p193)

/-- `O2|rj|Cmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1982). Erratum: ''Minimizing maximum lateness in a two-machine open shop''\ [Math. Oper. Res. \bf 6 (1981), no. 1, 153-158]. https://doi.org/10.1287/moor.6.1.153
-/
def p193_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p193)

/-- `O2||Lmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1981). Minimizing maximum lateness in a two-machine open shop. https://doi.org/10.1287/moor.6.1.153
-/
def p194_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p194)

/-- `O2||Lmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1982). Erratum: ''Minimizing maximum lateness in a two-machine open shop''\ [Math. Oper. Res. \bf 6 (1981), no. 1, 153-158]. https://doi.org/10.1287/moor.6.1.153
-/
def p194_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p194)

/-- `O2|fixj;rj|Cmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1981). Minimizing maximum lateness in a two-machine open shop. https://doi.org/10.1287/moor.6.1.153
-/
def p195_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p195)

/-- `O2|fixj;rj|Cmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1982). Erratum: ''Minimizing maximum lateness in a two-machine open shop''\ [Math. Oper. Res. \bf 6 (1981), no. 1, 153-158]. https://doi.org/10.1287/moor.6.1.153
-/
def p195_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p195)

/-- `O2|fixj|Lmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1981). Minimizing maximum lateness in a two-machine open shop. https://doi.org/10.1287/moor.6.1.153
-/
def p196_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p196)

/-- `O2|fixj|Lmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1982). Erratum: ''Minimizing maximum lateness in a two-machine open shop''\ [Math. Oper. Res. \bf 6 (1981), no. 1, 153-158]. https://doi.org/10.1287/moor.6.1.153
-/
def p196_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p196)

/-- `O2|Mj;rj|Cmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1981). Minimizing maximum lateness in a two-machine open shop. https://doi.org/10.1287/moor.6.1.153
-/
def p197_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p197)

/-- `O2|Mj;rj|Cmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1982). Erratum: ''Minimizing maximum lateness in a two-machine open shop''\ [Math. Oper. Res. \bf 6 (1981), no. 1, 153-158]. https://doi.org/10.1287/moor.6.1.153
-/
def p197_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p197)

/-- `O2|Mj|Lmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1981). Minimizing maximum lateness in a two-machine open shop. https://doi.org/10.1287/moor.6.1.153
-/
def p198_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p198)

/-- `O2|Mj|Lmax`: is strongly NP-hard.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1982). Erratum: ''Minimizing maximum lateness in a two-machine open shop''\ [Math. Oper. Res. \bf 6 (1981), no. 1, 153-158]. https://doi.org/10.1287/moor.6.1.153
-/
def p198_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p198)

/-- `O|pij=1;prec;no-wait|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p199_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p199)

/-- `F|Mj;prec;pij=1|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p200_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p200)

/-- `O|Mj;prec;pij=1|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p201_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p201)

/-- `J2||Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1979). Computational complexity of discrete optimization problems. https://doi.org/10.1016/s0167-5060(08)70821-5
-/
def p202_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p202)

/-- `J3|pij=1;rcrc|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1979). Computational complexity of discrete optimization problems. https://doi.org/10.1016/s0167-5060(08)70821-5
-/
def p203_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p203)

/-- `J3|Mj;pij=1|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1979). Computational complexity of discrete optimization problems. https://doi.org/10.1016/s0167-5060(08)70821-5
-/
def p204_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p204)

/-- `F2|chains|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p205_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p205)

/-- `F2|rj|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p206_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p206)

/-- `F2||Lmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p207_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p207)

/-- `F2|Mj|Cmax`: is NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p208_r0 (R : Reading F) : Prop :=
  NPHard (R.at p208)

/-- `F2|Mj;chains|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p209_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p209)

/-- `F2|Mj;rj|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p210_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p210)

/-- `F2|Mj|Lmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p211_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p211)

/-- `F|pij=1;prec|Cmax`: is strongly NP-hard.

Leung, J.Y.-T. and Vornberger, O. and Witthoff, J.D. (1984). On some variants of the bandwidth minimization problem. https://doi.org/10.1137/0213040
-/
def p212_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p212)

/-- `F|pij=1;prec|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p212_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p212)

/-- `O2|outtree;pij=1;rj|ΣCj`: is in P.

Lushchakova, I. (2006). Two machine preemptive scheduling problem with release dates, equal processing times and precedence constraints. https://doi.org/10.1016/j.ejor.2004.08.037
-/
def p213_r0 (R : Reading F) : Prop :=
  InP (R.at p213)

/-- `J|prec;rj;n=k|ΣwjUj`: is in Ppseudo.

Middendorf, M. and Timkovsky, V.G. (1999). Transversal graphs for partially ordered sets: sequencing, merging and scheduling problems. https://doi.org/10.1023/a:1009827520712

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p214_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p214) (lift (Ops.n p214))

/-- `J|prec;rj;n=k|ΣwjTj`: is in Ppseudo.

Middendorf, M. and Timkovsky, V.G. (1999). Transversal graphs for partially ordered sets: sequencing, merging and scheduling problems. https://doi.org/10.1023/a:1009827520712

Note: the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs.
-/
def p215_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p215) (lift (Ops.n p215))

/-- `F2|rj;no-wait|Cmax`: is strongly NP-hard.

Röck, H. (1984). Some new results in flow shop scheduling. https://doi.org/10.1007/bf01919082
-/
def p216_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p216)

/-- `F2|no-wait|Lmax`: is strongly NP-hard.

Röck, H. (1984). Some new results in flow shop scheduling. https://doi.org/10.1007/bf01919082
-/
def p217_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p217)

/-- `F2|no-wait|ΣCj`: is strongly NP-hard.

Röck, H. (1984). Some new results in flow shop scheduling. https://doi.org/10.1007/bf01919082
-/
def p218_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p218)

/-- `J2|no-wait|ΣCj`: is strongly NP-hard.

Röck, H. (1984). Some new results in flow shop scheduling. https://doi.org/10.1007/bf01919082
-/
def p219_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p219)

/-- `F3|no-wait|Cmax`: is strongly NP-hard.

Röck, H. (1984). The three-machine no-wait flow shop is NP-complete. https://doi.org/10.1145/62.65
-/
def p220_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p220)

/-- `O|pij=1;tjkl=T|Cmax`: is in P.

Rayward-Smith, V.J. and Rebaine, D. (1992). Open shop scheduling with delays. https://doi.org/10.1051/ita/1992260504391
-/
def p221_r0 (R : Reading F) : Prop :=
  InP (R.at p221)

/-- `O|pij=1;tkl=tlk|Cmax`: is strongly NP-hard.

Rayward-Smith, V.J. and Rebaine, D. (1992). Open shop scheduling with delays. https://doi.org/10.1051/ita/1992260504391
-/
def p222_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p222)

/-- `J|prec;rj;n=2|ΣwjUj`: is in P.

Sotskov, Y.N. (1991). The complexity of shop-scheduling problems with two or three jobs. https://doi.org/10.1016/0377-2217(91)90066-5
-/
def p223_r0 (R : Reading F) : Prop :=
  InP (R.at p223)

/-- `J|prec;rj;n=2|ΣwjTj`: is in P.

Sotskov, Y.N. (1991). The complexity of shop-scheduling problems with two or three jobs. https://doi.org/10.1016/0377-2217(91)90066-5
-/
def p224_r0 (R : Reading F) : Prop :=
  InP (R.at p224)

/-- `O2|no-wait|Cmax`: is strongly NP-hard.

Sahni, S. and Cho, Y. (1979). Complexity of scheduling shops with no wait in process. https://doi.org/10.1287/moor.4.4.448
-/
def p225_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p225)

/-- `J2|no-wait|Cmax`: is strongly NP-hard.

Sahni, S. and Cho, Y. (1979). Complexity of scheduling shops with no wait in process. https://doi.org/10.1287/moor.4.4.448
-/
def p226_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p226)

/-- `J3|pij=1;no-wait|Cmax`: is strongly NP-hard.

Sriskandarajah, C. and Ladet, P. (1986). Some no-wait shops scheduling problems: complexity aspect. https://doi.org/10.1016/0377-2217(86)90036-6
-/
def p227_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p227)

/-- `J3|pij=1;no-wait|ΣCj`: is strongly NP-hard.

Sriskandarajah, C. and Ladet, P. (1986). Some no-wait shops scheduling problems: complexity aspect. https://doi.org/10.1016/0377-2217(86)90036-6
-/
def p228_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p228)

/-- `J3|n=3|Cmax`: is NP-hard.

Sotskov, Y.N. and Shakhlevich, N.V. (1995). NP-hardness of shop-scheduling problems with three jobs. https://doi.org/10.1016/0166-218x(95)80004-n
-/
def p229_r0 (R : Reading F) : Prop :=
  NPHard (R.at p229)

/-- `J3|n=3|ΣCj`: is NP-hard.

Sotskov, Y.N. and Shakhlevich, N.V. (1995). NP-hardness of shop-scheduling problems with three jobs. https://doi.org/10.1016/0166-218x(95)80004-n
-/
def p230_r0 (R : Reading F) : Prop :=
  NPHard (R.at p230)

/-- `J3|fixj;n=3|Cmax`: is NP-hard.

Sotskov, Y.N. and Shakhlevich, N.V. (1995). NP-hardness of shop-scheduling problems with three jobs. https://doi.org/10.1016/0166-218x(95)80004-n
-/
def p231_r0 (R : Reading F) : Prop :=
  NPHard (R.at p231)

/-- `J3|fixj;n=3|ΣCj`: is NP-hard.

Sotskov, Y.N. and Shakhlevich, N.V. (1995). NP-hardness of shop-scheduling problems with three jobs. https://doi.org/10.1016/0166-218x(95)80004-n
-/
def p232_r0 (R : Reading F) : Prop :=
  NPHard (R.at p232)

/-- `J3|Mj;n=3|ΣCj`: is NP-hard.

Sotskov, Y.N. and Shakhlevich, N.V. (1995). NP-hardness of shop-scheduling problems with three jobs. https://doi.org/10.1016/0166-218x(95)80004-n
-/
def p233_r0 (R : Reading F) : Prop :=
  NPHard (R.at p233)

/-- `J2|chains;pij=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (1985). On the complexity of scheduling an arbitrary system. None
-/
def p234_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p234)

/-- `J2|Mj;chains;pij=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (1985). On the complexity of scheduling an arbitrary system. None
-/
def p235_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p235)

/-- `J2|pij=1;rj|Cmax`: is in P.

Timkovsky, V.G. (1997). A polynomial-time algorithm for the two-machine unit-time release-date job-shop schedule-length problem. https://doi.org/10.1016/s0166-218x(96)00106-0
-/
def p236_r0 (R : Reading F) : Prop :=
  InP (R.at p236)

/-- `J2|pij=1;rj|ΣUj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p237_r0 (R : Reading F) : Prop :=
  NPHard (R.at p237)

/-- `J2|pij=1;rj|ΣCj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p238_r0 (R : Reading F) : Prop :=
  NPHard (R.at p238)

/-- `J2|chains;pij=1|ΣCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p239_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p239)

/-- `J2|pij=1|ΣwjCj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p240_r0 (R : Reading F) : Prop :=
  NPHard (R.at p240)

/-- `J2|pij=1;rj|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p241_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p241)

/-- `J2|pij=1|ΣwjTj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p242_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p242)

/-- `J2|chains;pij=1;no-wait|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p243_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p243)

/-- `J2|pij=1;rj;no-wait|Lmax`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p244_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p244)

/-- `J2|chains;pij=1;no-wait|ΣCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p245_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p245)

/-- `J2|pij=1;rj;no-wait|ΣCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p246_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p246)

/-- `J2|pij=1;no-wait|ΣwjCj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p247_r0 (R : Reading F) : Prop :=
  NPHard (R.at p247)

/-- `J2|pij=1;no-wait|ΣwjTj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p248_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p248)

/-- `J2|fixj;rj;pij=1|ΣCj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p249_r0 (R : Reading F) : Prop :=
  NPHard (R.at p249)

/-- `J2|fixj;chains;pij=1|ΣCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p250_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p250)

/-- `J2|fixj;pij=1|ΣwjCj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p251_r0 (R : Reading F) : Prop :=
  NPHard (R.at p251)

/-- `J2|fixj;rj;pij=1|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p252_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p252)

/-- `J2|Mj;rj;pij=1|ΣCj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p253_r0 (R : Reading F) : Prop :=
  NPHard (R.at p253)

/-- `J2|Mj;chains;pij=1|ΣCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p254_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p254)

/-- `J2|Mj;pij=1|ΣwjCj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p255_r0 (R : Reading F) : Prop :=
  NPHard (R.at p255)

/-- `J2|Mj;rj;pij=1|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p256_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p256)

/-- `J2|Mj;rj;pij=1|ΣUj`: is NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p257_r0 (R : Reading F) : Prop :=
  NPHard (R.at p257)

/-- `J2|Mj;pij=1|ΣwjTj`: is strongly NP-hard.

Timkovsky, V.G. (1998). Is a unit-time job shop not easier than identical parallel machines?. https://doi.org/10.1016/s0166-218x(98)00032-8
-/
def p258_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p258)

/-- `O|pij=1;outtree;rj|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p259_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p259)

/-- `O|pij=1;prec|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p260_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p260)

/-- `O|pij=1;outtree|Lmax`: is *NP.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1

Note: the data writes *NP for the strong NP-hardness of the source (Timkovsky 2003, Table 5).
-/
def p261_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p261)

/-- `O2|pij=1;chains|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p262_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p262)

/-- `O3|pij=1;chains|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p263_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p263)

/-- `O2|pij=1;chains|ΣUj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p264_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p264)

/-- `O3|pij=1;chains|ΣUj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p265_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p265)

/-- `O2|pij=1;chains|ΣTj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p266_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p266)

/-- `O3|pij=1;chains|ΣTj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p267_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p267)

/-- `O|pij=1;rj;no-wait|ΣCj`: is in P.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p268_r0 (R : Reading F) : Prop :=
  InP (R.at p268)

/-- `O2|pij=1;chains;rj;no-wait|Cmax`: is in P.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p269_r0 (R : Reading F) : Prop :=
  InP (R.at p269)

/-- `O2|pij=1;chains;rj;no-wait|ΣCj`: is in P.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p270_r0 (R : Reading F) : Prop :=
  InP (R.at p270)

/-- `O2|pij=1;prec;no-wait|ΣCj`: is in P.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p271_r0 (R : Reading F) : Prop :=
  InP (R.at p271)

/-- `O|pij=1;rj;no-wait|ΣwjCj`, parameter m: is in P.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1

Note: in P for every fixed value.
-/
def p272_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p272) (lift (Ops.m p272))

/-- `O|pij=1;rj;no-wait|ΣTj`, parameter m: is in P.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1

Note: in P for every fixed value.
-/
def p273_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p273) (lift (Ops.m p273))

/-- `O2|pij=1;chains;no-wait|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p274_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p274)

/-- `O3|pij=1;chains;no-wait|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p275_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p275)

/-- `O2|pij=1;chains;no-wait|ΣUj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p276_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p276)

/-- `O3|pij=1;chains;no-wait|ΣUj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p277_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p277)

/-- `O2|pij=1;chains;no-wait|ΣTj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p278_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p278)

/-- `O3|pij=1;chains;no-wait|ΣTj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p279_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p279)

/-- `F|fixj;prec;pij=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p280_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p280)

/-- `O|fixj;prec;pij=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p281_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p281)

/-- `O|fixj;tree;rj;pij=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p282_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p282)

/-- `O|fixj;tree;pij=1|Lmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p283_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p283)

/-- `O2|fixj;chains;pij=1|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p284_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p284)

/-- `O2|fixj;chains;pij=1|ΣUj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p285_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p285)

/-- `O2|fixj;chains;pij=1|ΣTj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p286_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p286)

/-- `O|Mj;outtree;rj;pij=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p287_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p287)

/-- `O|Mj;prec;pij=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p288_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p288)

/-- `O|Mj;outtree;pij=1|Lmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p289_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p289)

/-- `O2|Mj;chains;pij=1|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p290_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p290)

/-- `O2|Mj;chains;pij=1|ΣUj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p291_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p291)

/-- `O2|Mj;chains;pij=1|ΣTj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p292_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p292)

/-- `O2|chains|Cmax`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p293_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p293)

/-- `F2|pij=1;chains|ΣwjCj`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p294_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p294)

/-- `F3|pij=1;chains|ΣwjCj`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p295_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p295)

/-- `F2|fixj;chains;pij=1|ΣwjCj`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p296_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p296)

/-- `O2|fixj;chains|Cmax`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p297_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p297)

/-- `F2|Mj;chains;pij=1|ΣwjCj`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p298_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p298)

/-- `O2|Mj;chains|Cmax`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p299_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p299)

/-- `O|pij=1;prec;no-wait|Cmax`: is strongly NP-hard.

Ullman, J.D. (1975). NP-complete scheduling problems. https://doi.org/10.1016/s0022-0000(75)80008-0
-/
def p300_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p300)

/-- `F|Mj;prec;pij=1|Cmax`: is strongly NP-hard.

Ullman, J.D. (1975). NP-complete scheduling problems. https://doi.org/10.1016/s0022-0000(75)80008-0
-/
def p301_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p301)

/-- `O2|pij=1;tj|Cmax`: is strongly NP-hard.

Yu, W. and Hoogeveen, H. and Lenstra, J.K. (2004). Minimizing makespan in a two-machine flow shop with delays and unit-time operations is NP-hard. https://doi.org/10.1023/b:josh.0000036858.59787.c2
-/
def p302_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p302)

/-- `O2|pij=1;tj|Cmax`: is strongly NP-hard.

Yu, W. (1996). The two-machine flow shop problem with delays and the one-machine total tardiness problem. None
-/
def p302_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p302)

/-- `F2|pij=1;tj∈T1,T2|Cmax`: is in P.

Yu, W. (1996). The two-machine flow shop problem with delays and the one-machine total tardiness problem. None
-/
def p303_r0 (R : Reading F) : Prop :=
  InP (R.at p303)

/-- `F2|tj∈T1,T2|Cmax`: is strongly NP-hard.

Yu, W. (1996). The two-machine flow shop problem with delays and the one-machine total tardiness problem. None
-/
def p304_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p304)

/-- `O2|tjkl=T|Cmax`: is NP-hard.

Yu, W. (1996). The two-machine flow shop problem with delays and the one-machine total tardiness problem. None
-/
def p305_r0 (R : Reading F) : Prop :=
  NPHard (R.at p305)

/-- `O2|tj∈T1,T2|Cmax`: is strongly NP-hard.

Yu, W. (1996). The two-machine flow shop problem with delays and the one-machine total tardiness problem. None
-/
def p306_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p306)

/-- `F|pij=1;rj|ΣwjUj`: is in P.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p307_r0 (R : Reading F) : Prop :=
  InP (R.at p307)

/-- `F|pij=1;rj|ΣwjTj`: is in P.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p308_r0 (R : Reading F) : Prop :=
  InP (R.at p308)

/-- `F2|fixj;chains;pij=1|ΣUj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p309_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p309)

/-- `F2|fixj;chains;pij=1|ΣTj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p310_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p310)

/-- `F2|Mj;chains;pij=1|ΣUj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p311_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p311)

/-- `F2|Mj;chains;pij=1|ΣTj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p312_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p312)

/-- `F|pij=1;tk;rj|ΣwjUj`: is in P.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p313_r0 (R : Reading F) : Prop :=
  InP (R.at p313)

/-- `F|pij=1;tk;rj|ΣwjTj`: is in P.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p314_r0 (R : Reading F) : Prop :=
  InP (R.at p314)

/-- `FF(1,m)||ΣZj`: is strongly NP-hard.

Heeger, Klaus and Hermelin, Danny and Itzhaki, Yuval and Schieber, Baruch and Shabtay, Dvir (2026). Just-in-Time Scheduling in Two-Stage Flexible Flow Shops. https://doi.org/10.1016/j.ejor.2026.02.017
-/
def p315_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p315)

/-- `FF(1,m)||ΣZj`, parameter m: is strongly W[2]-hard.

Heeger, Klaus and Hermelin, Danny and Itzhaki, Yuval and Schieber, Baruch and Shabtay, Dvir (2026). Just-in-Time Scheduling in Two-Stage Flexible Flow Shops. https://doi.org/10.1016/j.ejor.2026.02.017
-/
def p315_r1 (R : Reading F) : Prop :=
  StronglyWHard (R.at p315) 2 (lift (Ops.m p315))

/-- `FF(1,m)||ΣwjZj`, parameter m: is solvable in time O(W· n^m), where W is the total weight of the jobs.

Heeger, Klaus and Hermelin, Danny and Itzhaki, Yuval and Schieber, Baruch and Shabtay, Dvir (2026). Just-in-Time Scheduling in Two-Stage Flexible Flow Shops. https://doi.org/10.1016/j.ejor.2026.02.017

Note: stated with wide words, which hold the address of every step, as for every algorithm whose running time exceeds a polynomial; on the instances whose last operations have positive length, which the source assumes; and with the n log n of sorting the jobs, which the source's bound includes.
-/
def p316_r1 (R : Reading F) : Prop :=
  DecidesWithinWide ((R.at p316).restrict (Ops.lastPositive p316)) (fun x => (Ops.totalW p316 x.1) * (Ops.n p316 x.1) ^ (Ops.m p316 x.1) + (Ops.n p316 x.1) * Nat.log 2 (Ops.n p316 x.1))

/-- `FF(1,m)||ΣwjZj`, parameter qmax: is solvable in time O(W· m^qmax· n), where W is the total weight of the jobs.

Heeger, Klaus and Hermelin, Danny and Itzhaki, Yuval and Schieber, Baruch and Shabtay, Dvir (2026). Just-in-Time Scheduling in Two-Stage Flexible Flow Shops. https://doi.org/10.1016/j.ejor.2026.02.017

Note: stated with wide words, which hold the address of every step, as for every algorithm whose running time exceeds a polynomial; on the instances whose last operations have positive length, which the source assumes; and with the n log n of sorting the jobs, which the source's bound includes.
-/
def p316_r2 (R : Reading F) : Prop :=
  DecidesWithinWide ((R.at p316).restrict (Ops.lastPositive p316)) (fun x => (Ops.totalW p316 x.1) * (Ops.m p316 x.1) ^ (Ops.qmax p316 x.1) * (Ops.n p316 x.1) + (Ops.n p316 x.1) * Nat.log 2 (Ops.n p316 x.1))

/-- `FF(1,m)||ΣwjZj`, parameter χ: is solvable in time O(W· 2^χ· n), where W is the total weight of the jobs.

Heeger, Klaus and Hermelin, Danny and Itzhaki, Yuval and Schieber, Baruch and Shabtay, Dvir (2026). Just-in-Time Scheduling in Two-Stage Flexible Flow Shops. https://doi.org/10.1016/j.ejor.2026.02.017

Note: stated with wide words, which hold the address of every step, as for every algorithm whose running time exceeds a polynomial; on the instances whose last operations have positive length, which the source assumes; and with the n log n of sorting the jobs, which the source's bound includes.
-/
def p316_r3 (R : Reading F) : Prop :=
  DecidesWithinWide ((R.at p316).restrict (Ops.lastPositive p316)) (fun x => (Ops.totalW p316 x.1) * 2 ^ (Ops.chi p316 x.1) * (Ops.n p316 x.1) + (Ops.n p316 x.1) * Nat.log 2 (Ops.n p316 x.1))

/-- `FF(1,m)|pj=p|ΣZj`: is in P.

Heeger, Klaus and Hermelin, Danny and Itzhaki, Yuval and Schieber, Baruch and Shabtay, Dvir (2026). Just-in-Time Scheduling in Two-Stage Flexible Flow Shops. https://doi.org/10.1016/j.ejor.2026.02.017
-/
def p317_r0 (R : Reading F) : Prop :=
  InP (R.at p317)

/-- `F3||ΣZj`: is strongly NP-hard.

Choi, Byung-Cheon and Yoon, Suk-Hun (2007). Maximizing the Weighted Number of Just-in-Time Jobs in Flow Shop Scheduling. https://doi.org/10.1007/s10951-007-0030-z
-/
def p318_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p318)

/-- `F3||ΣwjZj`: is strongly NP-hard.

Choi, Byung-Cheon and Yoon, Suk-Hun (2007). Maximizing the Weighted Number of Just-in-Time Jobs in Flow Shop Scheduling. https://doi.org/10.1007/s10951-007-0030-z
-/
def p319_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p319)

/-- `F2||ΣwjZj`: is NP-hard.

Choi, Byung-Cheon and Yoon, Suk-Hun (2007). Maximizing the Weighted Number of Just-in-Time Jobs in Flow Shop Scheduling. https://doi.org/10.1007/s10951-007-0030-z
-/
def p320_r0 (R : Reading F) : Prop :=
  NPHard (R.at p320)

/-- `F2||ΣwjZj`: is in Ppseudo.

Shabtay, Dvir and Bensoussan, Yaron (2012). Maximizing the Weighted Number of Just-in-Time Jobs in Several Two-Machine Scheduling Systems. https://doi.org/10.1007/s10951-010-0204-y
-/
def p320_r1 (R : Reading F) : Prop :=
  PseudoPoly (R.at p320)

/-- `F2||ΣwjZj`: has an FPTAS.

Shabtay, Dvir and Bensoussan, Yaron (2012). Maximizing the Weighted Number of Just-in-Time Jobs in Several Two-Machine Scheduling Systems. https://doi.org/10.1007/s10951-010-0204-y

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p320_r2 (R : Reading F) : Prop :=
  FPTASKept (R.at p320) (Ops.totalW p320)

/-- `F2||ΣwjZj`, parameter #d: is W[1]-hard.

Hermelin, Danny and Shabtay, Dvir and Talmon, Nimrod (2019). On the Parameterized Tractability of the Just-in-Time Flow Shop Scheduling Problem. https://doi.org/10.1007/s10951-019-00617-7
-/
def p320_r3 (R : Reading F) : Prop :=
  WHard (R.at p320) 1 (lift (Ops.numD p320))

/-- `F2||ΣwjZj`, parameter #d+#w: is fixed parameter tractable.

Hermelin, Danny and Shabtay, Dvir and Talmon, Nimrod (2019). On the Parameterized Tractability of the Just-in-Time Flow Shop Scheduling Problem. https://doi.org/10.1007/s10951-019-00617-7
-/
def p320_r4 (R : Reading F) : Prop :=
  IsFPT (R.at p320) (tplus (lift (Ops.numD p320)) (lift (Ops.numW p320)))

/-- `F2||ΣwjZj`, parameter #d+#p: is fixed parameter tractable.

Hermelin, Danny and Shabtay, Dvir and Talmon, Nimrod (2019). On the Parameterized Tractability of the Just-in-Time Flow Shop Scheduling Problem. https://doi.org/10.1007/s10951-019-00617-7
-/
def p320_r5 (R : Reading F) : Prop :=
  IsFPT (R.at p320) (tplus (lift (Ops.numD p320)) (lift (Ops.numP p320)))

/-- `F2||ΣZj`: is in P.

Choi, Byung-Cheon and Yoon, Suk-Hun (2007). Maximizing the Weighted Number of Just-in-Time Jobs in Flow Shop Scheduling. https://doi.org/10.1007/s10951-007-0030-z
-/
def p321_r0 (R : Reading F) : Prop :=
  InP (R.at p321)

/-- `F||ΣCj`: is  APX-hard.

Hoogeveen, Han and Schuurman, Petra and Woeginger, Gerhard J (2001). Non-approximability results for scheduling problems with minsum criteria. https://doi.org/10.1287/ijoc.13.2.157.10520

Note: stated as the consequence: no PTAS unless P = NP.
-/
def p322_r0 (R : Reading F) : Prop :=
  NoPTAS (R.at p322)

/-- `O||ΣCj`: is  APX-hard.

Hoogeveen, Han and Schuurman, Petra and Woeginger, Gerhard J (2001). Non-approximability results for scheduling problems with minsum criteria. https://doi.org/10.1287/ijoc.13.2.157.10520

Note: stated as the consequence: no PTAS unless P = NP.
-/
def p323_r0 (R : Reading F) : Prop :=
  NoPTAS (R.at p323)

/-- `O|pij=1;STsd,b|Cmax`: is NP-hard.

van Bevern, René and Pyatkin, Artem V. (2016). Completing partial schedules for Open Shop with unit processing times and routing. https://doi.org/10.1007/978-3-319-34171-2_6
-/
def p326_r0 (R : Reading F) : Prop :=
  NPHard (R.at p326)

end Lax434175.ZooShopsResults
