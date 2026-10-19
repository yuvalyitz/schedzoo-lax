import Lax434175.ZooSerialBatching
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, serial batching problems
type: definition
---
The 33 results of The Scheduling Zoo on its serial batching problems that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooSerialBatchingResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters Lax434175.ZooSerialBatching

/-- `1|prec;pj=p;s-batch|ΣCj`: is in P.

Albers, S. and Brucker, P. (1993). The complexity of one-machine batching problems. https://doi.org/10.1016/0166-218x(93)90085-3
-/
def p0_r0 (R : Reading F) : Prop :=
  InP (R.at p0)

/-- `1|pj=p;s-batch|ΣwjCj`: is in P.

Albers, S. and Brucker, P. (1993). The complexity of one-machine batching problems. https://doi.org/10.1016/0166-218x(93)90085-3
-/
def p1_r0 (R : Reading F) : Prop :=
  InP (R.at p1)

/-- `1|chains;s-batch|ΣCj`: is NP-hard.

Albers, S. and Brucker, P. (1993). The complexity of one-machine batching problems. https://doi.org/10.1016/0166-218x(93)90085-3
-/
def p2_r0 (R : Reading F) : Prop :=
  NPHard (R.at p2)

/-- `1|chains;pj=1;s-batch|ΣwjCj`: is strongly NP-hard.

Albers, S. and Brucker, P. (1993). The complexity of one-machine batching problems. https://doi.org/10.1016/0166-218x(93)90085-3
-/
def p3_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p3)

/-- `1|s-batch|ΣwjCj`: is strongly NP-hard.

Albers, S. and Brucker, P. (1993). The complexity of one-machine batching problems. https://doi.org/10.1016/0166-218x(93)90085-3
-/
def p4_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p4)

/-- `1|pj=p;s-batch;rj|ΣwjCj`: is in P.

Baptiste, P. (2000). Batching identical jobs. https://doi.org/10.1007/s001860000088
-/
def p5_r0 (R : Reading F) : Prop :=
  InP (R.at p5)

/-- `1|pj=p;s-batch;rj|ΣwjUj`: is in P.

Baptiste, P. (2000). Batching identical jobs. https://doi.org/10.1007/s001860000088
-/
def p6_r0 (R : Reading F) : Prop :=
  InP (R.at p6)

/-- `1|pj=p;s-batch;rj|ΣTj`: is in P.

Baptiste, P. (2000). Batching identical jobs. https://doi.org/10.1007/s001860000088
-/
def p7_r0 (R : Reading F) : Prop :=
  InP (R.at p7)

/-- `1|s-batch|ΣTj`: is in Ppseudo.

Baptiste, P. and Jouglet, A. (2001). On minimizing total tardiness in a serial batching problem. https://doi.org/10.1051/ro:2001105
-/
def p8_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p8)

/-- `1|s-batch|ΣTj`: is NP-hard.

Du, J. and Leung, J.Y.-T. (1990). Minimizing total tardiness on one machine is NP-hard. https://doi.org/10.1287/moor.15.3.483
-/
def p8_r1 (R : Reading F) : Prop :=
  NPHard (R.at p8)

/-- `1|s-batch|ΣUj`: is in P.

Brucker, P. and Kovalyov, M.Y. (1996). Single machine batch scheduling to minimize the weighted number of late jobs. https://doi.org/10.1007/bf01303431
-/
def p9_r0 (R : Reading F) : Prop :=
  InP (R.at p9)

/-- `1|s-batch|ΣwjUj`: is in Ppseudo.

Brucker, P. and Kovalyov, M.Y. (1996). Single machine batch scheduling to minimize the weighted number of late jobs. https://doi.org/10.1007/bf01303431
-/
def p10_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p10)

/-- `1|s-batch|ΣwjUj`: is NP-hard.

Karp, R.M. (1972). Reducibility among combinatorial problems. https://doi.org/10.1007/978-1-4684-2001-2_9
-/
def p10_r1 (R : Reading F) : Prop :=
  NPHard (R.at p10)

/-- `1|s-batch|ΣCj`: is in P.

Coffman, Jr., E.G. and Yannakakis, M. and Magazine, M.J. and Santos, C. (1990). Batch sizing and job sequencing on a single machine. https://doi.org/10.1007/bf02248589
-/
def p11_r0 (R : Reading F) : Prop :=
  InP (R.at p11)

/-- `1|pj=p;s-batch|ΣwjUj`: is in P.

Hochbaum, D.S. and Landy, D. (1994). Scheduling with batching: minimizing the weighted number of tardy jobs. https://doi.org/10.1016/0167-6377(94)90063-9
-/
def p12_r0 (R : Reading F) : Prop :=
  InP (R.at p12)

/-- `1|prec;s-batch|ΣCj`: is strongly NP-hard.

Lawler, E.L. (1978). Sequencing jobs to minimize total weighted completion time subject to precedence constraints. https://doi.org/10.1016/s0167-5060(08)70323-6
-/
def p13_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p13)

/-- `1|prec;s-batch|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p13_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p13)

/-- `1|chains;pj=1;s-batch|ΣUj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1980). Complexity results for scheduling chains on a single machine. https://doi.org/10.1016/0377-2217(80)90111-3
-/
def p14_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p14)

/-- `1|s-batch;rj|Lmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p15_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p15)

/-- `1|s-batch;rj|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p16_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p16)

/-- `1|chains;pj=1;s-batch|ΣTj`: is strongly NP-hard.

Leung, J.Y.-T. and Young, G.H. (1990). Minimizing total tardiness on a single machine with precedence constraints. https://doi.org/10.1287/ijoc.2.4.346
-/
def p17_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p17)

/-- `1|prec;s-batch|Lmax`: is in P.

Ng, C.T. and Cheng, T.C.E. and Yuan, J.J. (2002). A note on the single machine serial batching scheduling problem to minimize maximum lateness with precedence constraints. https://doi.org/10.1016/s0167-6377(01)00105-5
-/
def p18_r0 (R : Reading F) : Prop :=
  InP (R.at p18)

/-- `1|s-batch(∞);rj|ΣwjUj`: is NP-hard.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9
-/
def p19_r0 (R : Reading F) : Prop :=
  NPHard (R.at p19)

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #d+#p: is W[1]-hard.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9
-/
def p19_r1 (R : Reading F) : Prop :=
  WHard (R.at p19) 1 (tplus (lift (Batch.numD p19)) (lift (Batch.numP p19)))

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #p+#r: is W[1]-hard.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9
-/
def p19_r2 (R : Reading F) : Prop :=
  WHard (R.at p19) 1 (tplus (lift (Batch.numP p19)) (lift (Batch.numR p19)))

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #d+#p+#w: is in P.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9

Note: in P for every fixed value.
-/
def p19_r3 (R : Reading F) : Prop :=
  InPFixed (R.at p19) (tplus (tplus (lift (Batch.numD p19)) (lift (Batch.numP p19))) (lift (Batch.numW p19)))

/-- `1|s-batch(∞);rj|ΣwjUj`, parameter #p+#r+#w: is in P.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9

Note: in P for every fixed value.
-/
def p19_r4 (R : Reading F) : Prop :=
  InPFixed (R.at p19) (tplus (tplus (lift (Batch.numP p19)) (lift (Batch.numR p19))) (lift (Batch.numW p19)))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #p: is in P.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9

Note: in P for every fixed value.
-/
def p20_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p20) (lift (Batch.numP p20))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #w: is in P.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9

Note: in P for every fixed value.
-/
def p20_r1 (R : Reading F) : Prop :=
  InPFixed (R.at p20) (lift (Batch.numW p20))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #d+#p: is fixed parameter tractable.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9
-/
def p20_r2 (R : Reading F) : Prop :=
  IsFPT (R.at p20) (tplus (lift (Batch.numD p20)) (lift (Batch.numP p20)))

/-- `1|s-batch(∞)|ΣwjUj`, parameter #d+#w: is fixed parameter tractable.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9
-/
def p20_r3 (R : Reading F) : Prop :=
  IsFPT (R.at p20) (tplus (lift (Batch.numD p20)) (lift (Batch.numW p20)))

/-- `1|s-batch(b)|ΣwjUj`, parameter #d+#w: is fixed parameter tractable.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9
-/
def p21_r0 (R : Reading F) : Prop :=
  IsFPT (R.at p21) (tplus (lift (Batch.numD p21)) (lift (Batch.numW p21)))

/-- `1|s-batch(b);rj|ΣwjUj`, parameter #d+#p+#r: is fixed parameter tractable.

Hermelin, Danny and Mnich, Matthias and Omlor, Simon (2024). Serial batching to minimize the weighted number of tardy jobs. https://link.springer.com/article/10.1007/s10951-024-00818-9
-/
def p22_r0 (R : Reading F) : Prop :=
  IsFPT (R.at p22) (tplus (tplus (lift (Batch.numD p22)) (lift (Batch.numP p22))) (lift (Batch.numR p22)))

end Lax434175.ZooSerialBatchingResults
