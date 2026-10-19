import Lax434175.ZooParallelBatching
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, parallel batching problems
type: definition
---
The 35 results of The Scheduling Zoo on its parallel batching problems that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooParallelBatchingResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters Lax434175.ZooParallelBatching

/-- `1|pj=p;p-batch;rj|ΣwjCj`: is in P.

Baptiste, P. (2000). Batching identical jobs. https://doi.org/10.1007/s001860000088
-/
def p0_r0 (R : Reading F) : Prop :=
  InP (R.at p0)

/-- `1|pj=p;p-batch;rj|ΣwjUj`: is in P.

Baptiste, P. (2000). Batching identical jobs. https://doi.org/10.1007/s001860000088
-/
def p1_r0 (R : Reading F) : Prop :=
  InP (R.at p1)

/-- `1|pj=p;p-batch;rj|ΣTj`: is in P.

Baptiste, P. (2000). Batching identical jobs. https://doi.org/10.1007/s001860000088
-/
def p2_r0 (R : Reading F) : Prop :=
  InP (R.at p2)

/-- `1|pj=p;p-batch(∞);rj|ΣwjTj`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p3_r0 (R : Reading F) : Prop :=
  InP (R.at p3)

/-- `1|p-batch(∞);rj|ΣwjTj`: is in Ppseudo.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p4_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p4)

/-- `1|p-batch(∞);rj|ΣwjUj`: is in Ppseudo.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p5_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p5)

/-- `1|p-batch|Cmax`: is in P.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p6_r0 (R : Reading F) : Prop :=
  InP (R.at p6)

/-- `1|p-batch(∞)|ΣwjCj`: is in P.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p7_r0 (R : Reading F) : Prop :=
  InP (R.at p7)

/-- `1|p-batch(∞)|ΣUj`: is in P.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p8_r0 (R : Reading F) : Prop :=
  InP (R.at p8)

/-- `1|p-batch(∞)|ΣwjUj`: is in Ppseudo.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p9_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p9)

/-- `1|p-batch(∞)|ΣwjUj`: is NP-hard.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p9_r1 (R : Reading F) : Prop :=
  NPHard (R.at p9)

/-- `1|p-batch(∞)|ΣwjTj`: is in Ppseudo.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p10_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p10)

/-- `1|p-batch(∞)|ΣwjTj`: is NP-hard.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p10_r1 (R : Reading F) : Prop :=
  NPHard (R.at p10)

/-- `1|p-batch;rj|Cmax`: is strongly NP-hard.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p11_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p11)

/-- `1|p-batch|Lmax`: is strongly NP-hard.

Brucker, P. and Gladky, A. and Hoogeveen, H. and Kovalyov, M.Y. and Potts, C.N. and Tautenhahn, T. and van de Velde, S.L. (1998). Scheduling a batching machine. https://doi.org/10.1002/(sici)1099-1425(199806)1:1<31::aid-jos4>3.0.co;2-r
-/
def p12_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p12)

/-- `1|prec;pj=p;p-batch(∞)|ΣwjUj`: is in P.

unknown author (unknown year). see: Earliest Start Schedule. None
-/
def p13_r0 (R : Reading F) : Prop :=
  InP (R.at p13)

/-- `1|prec;pj=p;p-batch(∞)|ΣwjTj`: is in P.

unknown author (unknown year). see: Earliest Start Schedule. None
-/
def p14_r0 (R : Reading F) : Prop :=
  InP (R.at p14)

/-- `1|tree;pj=p;p-batch|Cmax`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p15_r0 (R : Reading F) : Prop :=
  InP (R.at p15)

/-- `1|outtree;pj=p;p-batch;rj|Cmax`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p16_r0 (R : Reading F) : Prop :=
  InP (R.at p16)

/-- `1|intree;pj=p;p-batch|Lmax`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p17_r0 (R : Reading F) : Prop :=
  InP (R.at p17)

/-- `1|pj=1;p-batch;chains;rj|Lmax`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p18_r0 (R : Reading F) : Prop :=
  InP (R.at p18)

/-- `1|pj=1;p-batch;outtree;rj|ΣCj`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p19_r0 (R : Reading F) : Prop :=
  InP (R.at p19)

/-- `1|pj=p;p-batch;tree|ΣCj`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p20_r0 (R : Reading F) : Prop :=
  InP (R.at p20)

/-- `1|pj=p;p-batch|ΣwjTj`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p21_r0 (R : Reading F) : Prop :=
  InP (R.at p21)

/-- `1|pj=1;p-batch;rj|ΣwjTj`: is in P.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p22_r0 (R : Reading F) : Prop :=
  InP (R.at p22)

/-- `1|intree;pj=1;p-batch;rj|Cmax`: is strongly NP-hard.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p23_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p23)

/-- `1|prec;pj=1;p-batch|Cmax`: is strongly NP-hard.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p24_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p24)

/-- `1|outtree;pj=1;p-batch|Lmax`: is strongly NP-hard.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p25_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p25)

/-- `1|prec;pj=1;p-batch|ΣCj`: is strongly NP-hard.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p26_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p26)

/-- `1|intree;pj=1;p-batch;rj|ΣCj`: is strongly NP-hard.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p27_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p27)

/-- `1|chains;pj=1;p-batch|ΣwjCj`: is strongly NP-hard.

unknown author (unknown year). see: Parallel Machine Problem. None
-/
def p28_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p28)

/-- `1|p-batch;rj|ΣCj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p29_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p29)

/-- `1|chains;pj=1;p-batch|ΣUj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p30_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p30)

/-- `1|chains;pj=1;p-batch|ΣTj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p31_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p31)

/-- `1|p-batch;sizej|ΣCj`: is NP-complete.

Uzsoy, Reha (1994). Scheduling a single batch processing machine with non-identical job sizes. https://doi.org/10.1080/00207549408957026

Note: membership in NP is not stated.
-/
def p32_r0 (R : Reading F) : Prop :=
  NPHard (R.at p32)

end Lax434175.ZooParallelBatchingResults
