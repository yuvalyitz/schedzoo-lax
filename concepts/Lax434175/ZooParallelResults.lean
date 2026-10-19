import Lax434175.ZooParallel
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, non-preemptive problems on parallel machines
type: definition
---
The 381 results of The Scheduling Zoo on its non-preemptive problems on parallel machines that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooParallelResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters Lax434175.ZooParallel

/-- `P||Cmax`: has an (1+epsilon)-approximation in time 2^O(1/epsilon^2)log^3(1/epsilon) + O(nlog n).

Klaus Jansen (2010). An EPTAS for scheduling jobs on uniform processors: using an MILP relaxation with a constant number of integral variables. https://doi.org/10.1137/090749451
-/
def p0_r0 (R : Reading F) : Prop :=
  ∃ a : ℕ, SchemeWithin (R.at p0) (fun ε x => 2 ^ (a * ⌈1 / ε⌉₊ ^ 2) * Nat.log 2 ⌈1 / ε⌉₊ ^ 3 + (Ops.n p0 x) * Nat.log 2 (Ops.n p0 x))

/-- `P||Cmax`: under the exponential time hypothesis (ETH) there is no (1+epsilon)-approximation running in time 2^(1/epsilon)^1-delta +poly(n) for any delta>0.

L. Chen and K. Jansen and G. Zhang (2014). On the optimality of approximation schemes for the classical scheduling problem. https://doi.org/10.1137/1.9781611973402.50

Note: stated for one program reading ε, which the claim implies.
-/
def p0_r1 (R : Reading F) : Prop :=
  ETH → ∀ δ : ℚ, 0 < δ → ∀ d : ℕ, ¬ SchemeWithin (R.at p0) (fun ε x => 2 ^ ⌈((1 / ε : ℚ) : ℝ) ^ ((1 - δ : ℚ) : ℝ)⌉₊ + ((Ops.n p0 x) + 1) ^ d + inputSize (R.at p0) x)

/-- `P||Cmax`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. (1978). Strong NP-completeness results: motivation, examples, and implications. https://doi.org/10.1145/322077.322090
-/
def p0_r2 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p0)

/-- `P||Cmax`: has a deterministic O(2^O(1/epsilon log^2 (1/epsilon))) time algorithm.

Jansen, Klaus and Rohwedder, Lars (2022). On integer programming, discrepancy, and convolution. https://doi.org/10.1287/moor.2022.1308

Note: an approximation scheme; the dependence on n, not in the wording, is stated as a polynomial.
-/
def p0_r3 (R : Reading F) : Prop :=
  ∃ a d : ℕ, SchemeWithin (R.at p0) (fun ε x => 2 ^ (a * ⌈1 / ε⌉₊ * Nat.log 2 ⌈1 / ε⌉₊ ^ 2) + ((Ops.n p0 x) + 1) ^ d)

/-- `P||Cmax`: for any delta>0 there is no PTAS in time 2^O((1/epsilon)^1-delta) under the exponential time hypothesis (ETH).

Chen, Lin and Jansen, Klaus and Zhang, Guochuan (2018). On the optimality of exact and approximation algorithms for scheduling problems. https://doi.org/10.1016/j.jcss.2018.03.005

Note: stated for one program reading ε, with a polynomial factor in n.
-/
def p0_r4 (R : Reading F) : Prop :=
  ETH → ∀ δ : ℚ, 0 < δ → ∀ a d : ℕ, ¬ SchemeWithin (R.at p0) (fun ε x => 2 ^ (a * ⌈((1 / ε : ℚ) : ℝ) ^ ((1 - δ : ℚ) : ℝ)⌉₊) * ((Ops.n p0 x) + 1) ^ d + inputSize (R.at p0) x)

/-- `P||Cmax`: has a deterministic O(2^O(1/epsilon log(1/epsilon)loglog(1/epsilon))) time algorithm.

Berndt, Sebastian and Deppert, Max A and Jansen, Klaus and Rohwedder, Lars (2022). Load balancing: The long road from theory to practice. https://doi.org/10.1137/1.9781611977042.9

Note: an approximation scheme; the dependence on n, not in the wording, is stated as a polynomial.
-/
def p0_r5 (R : Reading F) : Prop :=
  ∃ a d : ℕ, SchemeWithin (R.at p0) (fun ε x => 2 ^ (a * ⌈1 / ε⌉₊ * Nat.log 2 ⌈1 / ε⌉₊ * Nat.log 2 (Nat.log 2 ⌈1 / ε⌉₊)) + ((Ops.n p0 x) + 1) ^ d)

/-- `P||Cmax`: has an additive approximation scheme with additive error epsilon pmax in time O(m^O(2^1/epsilon· n^O(1/epsilon· 2^1/epsilon))).

Buchem, Moritz and Rohwedder, Lars and Vredeveld, Tjark and Wiese, Andreas (2021). Additive Approximation Schemes for Load Balancing Problems. None

Note: an additive scheme with error ε p_max; the running time, polynomial for each fixed ε, is not stated.
-/
def p0_r6 (R : Reading F) : Prop :=
  AddScheme (R.at p0) (fun x => (((Ops.pmax p0) x : ℕ) : ℝ))

/-- `P||Cmax`, parameter m: has no 2^o(n) T^o(m)-time algorithm where T = Σ_j=1^n pj (under ETH).

Bringmann, Karl and Dürr, Anita and Węgrzycki, Karol (2026). Tight (S)ETH-based Lower Bounds for Pseudopolynomial Algorithms for Bin Packing and Multi-Machine Scheduling. https://doi.org/10.1145/3798129.3800913
-/
def p0_r7 (R : Reading F) : Prop :=
  ETH → ∀ f g : ℕ → ℕ, LittleO f id → LittleO g id → ¬ DecidesWithin (R.at p0) (fun x => 2 ^ f (Ops.n p0 x) * (Ops.totalP p0 x) ^ g (Ops.m p0 x) + inputSize (R.at p0) x)

/-- `P||Cmax`, parameter m: is W[1]-hard.

Knop, Dušan and Koutecký, Martin (2017). Scheduling meets n-fold integer programming. https://doi.org/10.48550/arXiv.1603.02611

Note: stated strongly: the source proves W[1]-hardness with the numbers in unary (Theorem 3); with binary numbers the problem is NP-hard already for two machines.
-/
def p0_r8 (R : Reading F) : Prop :=
  StronglyWHard (R.at p0) 1 (lift (Ops.m p0))

/-- `P||Cmax`, parameter pmax: is fixed parameter tractable.

Mnich, Matthias and Wiese, Andreas (2015). Scheduling and fixed-parameter tractability. https://doi.org/10.1007/s10107-014-0830-9
-/
def p0_r9 (R : Reading F) : Prop :=
  IsFPT (R.at p0) (lift (Ops.pmax p0))

/-- `P||Cmax`, parameter #p: is fixed parameter tractable.

Koutecký, Martin and Zink, Johannes (2025). Complexity of scheduling few types of jobs on related and unrelated machines. https://doi.org/10.1007/s10951-024-00827-8
-/
def p0_r10 (R : Reading F) : Prop :=
  IsFPT (R.at p0) (lift (Ops.numP p0))

/-- `P|rj|Cmax`, parameter m: has no 2^o(n) T^m-1-varepsilon-time algorithm for any varepsilon >0, where T = Σ_j=1^n pj (under ETH).

Bringmann, Karl and Dürr, Anita and Węgrzycki, Karol (2026). Tight (S)ETH-based Lower Bounds for Pseudopolynomial Algorithms for Bin Packing and Multi-Machine Scheduling. https://doi.org/10.1145/3798129.3800913
-/
def p1_r0 (R : Reading F) : Prop :=
  ETH → ∀ ε : ℚ, 0 < ε → ∀ f : ℕ → ℕ, LittleO f id → ¬ DecidesWithin (R.at p1) (fun x => 2 ^ f (Ops.n p1 x) * ⌊((Ops.totalP p1 x) : ℝ) ^ (((Ops.m p1 x) : ℝ) - 1 - ε)⌋₊ + inputSize (R.at p1) x)

/-- `P||ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p2_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p2)

/-- `P||ΣwjCj`, parameter m: has no 2^o(n) T^m-1-varepsilon-time algorithm for any varepsilon >0, where T = Σ_j=1^n pj (under ETH).

Bringmann, Karl and Dürr, Anita and Węgrzycki, Karol (2026). Tight (S)ETH-based Lower Bounds for Pseudopolynomial Algorithms for Bin Packing and Multi-Machine Scheduling. https://doi.org/10.1145/3798129.3800913
-/
def p2_r1 (R : Reading F) : Prop :=
  ETH → ∀ ε : ℚ, 0 < ε → ∀ f : ℕ → ℕ, LittleO f id → ¬ DecidesWithin (R.at p2) (fun x => 2 ^ f (Ops.n p2 x) * ⌊((Ops.totalP p2 x) : ℝ) ^ (((Ops.m p2 x) : ℝ) - 1 - ε)⌋₊ + inputSize (R.at p2) x)

/-- `P||ΣwjCj`, parameter m: is W[1]-hard.

Knop, Dušan and Koutecký, Martin (2017). Scheduling meets n-fold integer programming. https://doi.org/10.48550/arXiv.1603.02611

Note: stated strongly: the source proves W[1]-hardness with the numbers in unary (Theorem 3); with binary numbers the problem is NP-hard already for two machines.
-/
def p2_r2 (R : Reading F) : Prop :=
  StronglyWHard (R.at p2) 1 (lift (Ops.m p2))

/-- `P||ΣUj`, parameter m: has no 2^o(n) T^m-1-varepsilon-time algorithm for any varepsilon >0, where T = Σ_j=1^n pj (under ETH).

Bringmann, Karl and Dürr, Anita and Węgrzycki, Karol (2026). Tight (S)ETH-based Lower Bounds for Pseudopolynomial Algorithms for Bin Packing and Multi-Machine Scheduling. https://doi.org/10.1145/3798129.3800913
-/
def p3_r0 (R : Reading F) : Prop :=
  ETH → ∀ ε : ℚ, 0 < ε → ∀ f : ℕ → ℕ, LittleO f id → ¬ DecidesWithin (R.at p3) (fun x => 2 ^ f (Ops.n p3 x) * ⌊((Ops.totalP p3 x) : ℝ) ^ (((Ops.m p3 x) : ℝ) - 1 - ε)⌋₊ + inputSize (R.at p3) x)

/-- `P||ΣwjUj`, parameter m: has no 2^o(n) T^m-varepsilon-time algorithm for any varepsilon >0, where T = Σ_j=1^n pj (under ETH).

Bringmann, Karl and Dürr, Anita and Węgrzycki, Karol (2026). Tight (S)ETH-based Lower Bounds for Pseudopolynomial Algorithms for Bin Packing and Multi-Machine Scheduling. https://doi.org/10.1145/3798129.3800913
-/
def p4_r0 (R : Reading F) : Prop :=
  ETH → ∀ ε : ℚ, 0 < ε → ∀ f : ℕ → ℕ, LittleO f id → ¬ DecidesWithin (R.at p4) (fun x => 2 ^ f (Ops.n p4 x) * ⌊((Ops.totalP p4 x) : ℝ) ^ (((Ops.m p4 x) : ℝ) - ε)⌋₊ + inputSize (R.at p4) x)

/-- `R||Cmax`: the approximation ratio is at least 3/2 unless P=NP.

J. K. Lenstra, D. Shmoys and E. Tardos (1990). Approximation algorithms for scheduling unrelated parallel machines. https://doi.org/10.1007/bf01585745
-/
def p5_r0 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p5) ((3 : ℝ) / 2)

/-- `R||Cmax`: has a polynomial time 2-approximation.

J. K. Lenstra, D. Shmoys and E. Tardos (1990). Approximation algorithms for scheduling unrelated parallel machines. https://doi.org/10.1007/bf01585745
-/
def p5_r1 (R : Reading F) : Prop :=
  Approx (R.at p5) (const (2 : ℝ))

/-- `R||Cmax`: polynomial time approximation ratio ≥3/2.

Lenstra, Jan Karel and Shmoys, David B and Tardos, Éva (1990). Approximation algorithms for scheduling unrelated parallel machines. https://doi.org/10.1007/bf01585745

Note: read as holding unless P = NP.
-/
def p5_r2 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p5) ((3 : ℝ) / 2)

/-- `R||Cmax`, parameter pmax+rank((pij)): is fixed parameter tractable.

Chen, Lin and Marx, Dániel and Ye, Deshi and Zhang, Guochuan (2017). Parameterized and approximation results for scheduling with a low rank processing time matrix. https://doi.org/10.4230/LIPIcs.STACS.2017.22
-/
def p5_r3 (R : Reading F) : Prop :=
  IsFPT (R.at p5) (tplus (lift (Ops.pmax p5)) (lift (Ops.rank p5)))

/-- `R||Cmax`, parameter pmax+#kind: is fixed parameter tractable.

Knop, Dušan and Koutecký, Martin (2017). Scheduling meets n-fold integer programming. https://doi.org/10.48550/arXiv.1603.02611
-/
def p5_r4 (R : Reading F) : Prop :=
  IsFPT (R.at p5) (tplus (lift (Ops.pmax p5)) (lift (Ops.kinds p5)))

/-- `R||Cmax`, parameter #p+m: is fixed parameter tractable.

Mnich, Matthias and Wiese, Andreas (2015). Scheduling and fixed-parameter tractability. https://doi.org/10.1007/s10107-014-0830-9
-/
def p5_r5 (R : Reading F) : Prop :=
  IsFPT (R.at p5) (tplus (lift (Ops.numP p5)) (lift (Ops.m p5)))

/-- `Q|online-rj|Fmax`: has competitive ratio at most 25/3 by a dynamic posted pricing algorithm.

Sungjin Im and Benjamin Moseley and Kirk Pruhs and Clifford Stein (2017). Minimizing Maximum Flow Time on Related Machines via Immediate Dispatch and Dynamic Pricing. None

Note: read as deterministic.
-/
def p6_r0 (R : Reading F) : Prop :=
  DetCompetitive (R.at p6) (const ((25 : ℝ) / 3))

/-- `Q|online-rj|Fmax`: has competitive ratio at most 13.5.

Nikhil Bansal and Bouke Cloostermans (2015). Minimizing maximum flow-time on related machines. None

Note: read as deterministic.
-/
def p6_r1 (R : Reading F) : Prop :=
  DetCompetitive (R.at p6) (const (13.5 : ℝ))

/-- `R|rj|ΣwjCj`: has a polynomial time approximation ratio < 1.8786 by LP-rounding.

Sungjin Im and Shi Li (2017). Better Unrelated Machine Scheduling for Weighted Completion Time via Random sets from Non-Uniform Distributions. https://doi.org/10.1109/focs.2016.23
-/
def p9_r0 (R : Reading F) : Prop :=
  ∃ ρ : ℝ, ρ < (1.8786 : ℝ) ∧ Approx (R.at p9) (const ρ)

/-- `R|rj|ΣwjCj`: randomized approximation ratio ≤2+epsilon.

Schulz, Andreas S and Skutella, Martin (1997). Scheduling-LPs bear probabilities randomized approximations for min-sum criteria. https://doi.org/10.1007/3-540-63397-9_32
-/
def p9_r1 (R : Reading F) : Prop :=
  ∀ ε : ℚ, 0 < ε → RandomApprox (R.at p9) (const (2 + ε))

/-- `R|rj|ΣwjCj`, parameter m: has a PTAS.

Afrati, Foto and Bampis, Evripidis and Chekuri, Chandra and Karger, David and Kenyon, Claire and Khanna, Sanjeev and Milis, Ioannis and Queyranne, Maurice and Skutella, Martin and Stein, Clifford and others (1999). Approximation schemes for minimizing average weighted completion time with release dates. https://doi.org/10.1109/sffcs.1999.814574

Note: a PTAS for every fixed value.
-/
def p9_r2 (R : Reading F) : Prop :=
  PTASFixed (R.at p9) (Ops.m p9)

/-- `1|online-rj;pj=1;dj≤rj+4|ΣwjUj`: has competitive ratio Phi, the golden ratio.

Martin Böhm and Marek Chrobak and Lukasz Jez and Fei Li and Jiri Sgall and Pavel Vesely (2017). Online Packet Scheduling with Bounded Delay and Lookahead. None

Note: read as deterministic; measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p10_r0 (R : Reading F) : Prop :=
  DetCompetitiveKept (R.at p10) (Ops.totalW p10) (const ((1 + Real.sqrt 5) / 2))

/-- `1|online-rj;pj=1|ΣwjUj`: scheduling always the heaviest job is 2-competitive.

Bruce Hajek (2001). On the competitiveness of on-line scheduling of unit-length packets with hard deadlines in slotted time. None

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p11_r0 (R : Reading F) : Prop :=
  DetCompetitiveKept (R.at p11) (Ops.totalW p11) (const (2 : ℝ))

/-- `1|online-rj;pj=1|ΣwjUj`: scheduling always the heaviest job is 2-competitive.

Alexander Kesselman and Zvi Lotker and Yishay Mansour and Boaz Patt-Shamir and Baruch Schieber and Maxim Sviridenko (2004). Buffer overflow management in QoS switches. https://doi.org/10.1137/s0097539701399666

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p11_r1 (R : Reading F) : Prop :=
  DetCompetitiveKept (R.at p11) (Ops.totalW p11) (const (2 : ℝ))

/-- `1|online-rj;pj=1|ΣwjUj`: has competitive ratio at most 2sqrt2-1approx1.828.

Matthias Englert and Matthias Westermann (2007). Considering suppressed packets improves buffer management in QoS switches. None

Note: read as deterministic; measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p11_r2 (R : Reading F) : Prop :=
  DetCompetitiveKept (R.at p11) (Ops.totalW p11) (const (2 * Real.sqrt 2 - 1))

/-- `1|online-rj;pj=1;dj≤rj+2|ΣwjUj`: has competitive ratio at least Phi, the golden ratio.

Bruce Hajek (2001). On the competitiveness of on-line scheduling of unit-length packets with hard deadlines in slotted time. None

Note: read as deterministic; measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p12_r0 (R : Reading F) : Prop :=
  DetLowerBoundKept (R.at p12) (Ops.totalW p12) ((1 + Real.sqrt 5) / 2)

/-- `1|online-rj;pj=1;dj≤rj+2|ΣwjUj`: has competitive ratio Phi, the golden ratio.

Alexander Kesselman and Zvi Lotker and Yishay Mansour and Boaz Patt-Shamir and Baruch Schieber and Maxim Sviridenko (2004). Buffer overflow management in QoS switches. https://doi.org/10.1137/s0097539701399666

Note: read as deterministic; measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p12_r1 (R : Reading F) : Prop :=
  DetCompetitiveKept (R.at p12) (Ops.totalW p12) (const ((1 + Real.sqrt 5) / 2))

/-- `1|online-rj;pj=1;dj≤rj+2|ΣwjUj`: has competitive ratio at least Phiapprox1.618, the golden ratio.

Nir Andelman and Yishay Mansour and An Zhu (2003). Competitive queueing policies for QoS switches. None

Note: read as deterministic; measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p12_r2 (R : Reading F) : Prop :=
  DetLowerBoundKept (R.at p12) (Ops.totalW p12) ((1 + Real.sqrt 5) / 2)

/-- `1|online-rj;pj=1;dj≤rj+2|ΣwjUj`: has competitive ratio at least Phiapprox1.618, the golden ratio.

Francis Y. L. Chin and Stanley P. Y. Fung (2003). Online scheduling with partial job values: Does timesharing or randomization help?. https://doi.org/10.1007/s00453-003-1025-6

Note: read as deterministic; measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p12_r3 (R : Reading F) : Prop :=
  DetLowerBoundKept (R.at p12) (Ops.totalW p12) ((1 + Real.sqrt 5) / 2)

/-- `1|online-rj;pj=1;dj≤rj+3|ΣwjUj`: has competitive ratio Phiapprox1.618.

Francis Y. L. Chin and Stanley P. Y. Fung (2003). Online scheduling with partial job values: Does timesharing or randomization help?. https://doi.org/10.1007/s00453-003-1025-6

Note: read as deterministic; measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p13_r0 (R : Reading F) : Prop :=
  DetCompetitiveKept (R.at p13) (Ops.totalW p13) (const ((1 + Real.sqrt 5) / 2))

/-- `Q||Cmax`: has an (1+epsilon)-approximation in time 2^O(1/epsilon)log^4(1/epsilon) + O(n).

K. Jansen and K. M. Klein and and J. Verschae (2016). Closing the gap for makespan scheduling via sparsification techniques. None
-/
def p14_r0 (R : Reading F) : Prop :=
  ∃ a : ℕ, SchemeWithin (R.at p14) (fun ε x => 2 ^ (a * ⌈1 / ε⌉₊) * Nat.log 2 ⌈1 / ε⌉₊ ^ 4 + (Ops.n p14 x))

/-- `Q||Cmax`, parameter pmax: can be solved in time pmax^O(#p) n^O(1), where #p is the number of distinct processing times.

Lars Rohwedder (2025). ETH-Tight FPT Algorithm for Makespan Minimization on Uniform Machines. None
-/
def p14_r1 (R : Reading F) : Prop :=
  ∃ a b : ℕ, DecidesWithin (R.at p14) (fun x => (Ops.pmax p14 x) ^ (a * (Ops.numP p14 x)) * ((Ops.n p14 x) + 1) ^ b)

/-- `Q||Cmax`, parameter pmax: can be solved in time pmax^O(#p^2) n^O(1), where #p is the number of distinct processing times.

Kouteckỳ, Martin and Zink, Johannes (2025). Complexity of scheduling few types of jobs on related and unrelated machines. https://doi.org/10.1007/s10951-024-00827-8
-/
def p14_r2 (R : Reading F) : Prop :=
  ∃ a b : ℕ, DecidesWithin (R.at p14) (fun x => (Ops.pmax p14 x) ^ (a * (Ops.numP p14 x) ^ 2) * ((Ops.n p14 x) + 1) ^ b)

/-- `Q||Cmax`, parameter pmax: cannot be solved in time pmax^O(#p^0.99) n^O(1) under the Exponential time hypothesis. Here #p is the number of distinct processing times.

Chen, Lin and Jansen, Klaus and Zhang, Guochuan (2014). On the optimality of approximation schemes for the classical scheduling problem. https://doi.org/10.1137/1.9781611973402.50
-/
def p14_r3 (R : Reading F) : Prop :=
  ETH → ∀ a d : ℕ, ¬ DecidesWithin (R.at p14) (fun x => (Ops.pmax p14 x) ^ (a * ⌈((Ops.numP p14 x) : ℝ) ^ (0.99 : ℝ)⌉₊) * ((Ops.n p14 x) + 1) ^ d + inputSize (R.at p14) x)

/-- `Q||Cmax`, parameter pmax: is fixed parameter tractable.

Knop, Dušan and Koutecký, Martin (2017). Scheduling meets n-fold integer programming. https://doi.org/10.48550/arXiv.1603.02611
-/
def p14_r4 (R : Reading F) : Prop :=
  IsFPT (R.at p14) (lift (Ops.pmax p14))

/-- `Q||Cmax`, parameter #p: is W[1]-hard.

Koutecký, Martin and Zink, Johannes (2025). Complexity of scheduling few types of jobs on related and unrelated machines. https://doi.org/10.1007/s10951-024-00827-8

Note: stated strongly: the source proves it with n, the processing times and the speeds in unary (Theorem 4.15).
-/
def p14_r5 (R : Reading F) : Prop :=
  StronglyWHard (R.at p14) 1 (lift (Ops.numP p14))

/-- `1|prec|ΣwjCj`: has a polynomial time 2-approximation, by solving a linear program (LP) and doing list scheduling in order of completion times in the LP solution.

Andreas S. Schulz (1996). Scheduling to minimize total weighted completion time: Performance guarantees of LP-based heuristics and lower bounds. https://doi.org/10.1007/3-540-61310-2_23
-/
def p15_r0 (R : Reading F) : Prop :=
  Approx (R.at p15) (const (2 : ℝ))

/-- `1|prec|ΣwjCj`: deterministic approximation ratio ≤2.

Chekuri, Chandra and Motwani, Rajeev (1999). Precedence constrained scheduling to minimize sum of weighted completion times on a single machine. https://doi.org/10.1016/s0166-218x(98)00143-7
-/
def p15_r2 (R : Reading F) : Prop :=
  Approx (R.at p15) (const (2 : ℝ))

/-- `1|prec|ΣwjCj`: has a polynomial-time 2-approximation, by solving a linear program (LP) and doing list scheduling in order of completion times in the LP solution.

Leslie A. Hall and Andreas S. Schulz and David B. Shmoys and Joel Wein (1997). Scheduling to Minimize Average Completion Time: Off-Line and On-Line Approximation Algorithms. https://doi.org/10.1287/moor.22.3.513
-/
def p15_r3 (R : Reading F) : Prop :=
  Approx (R.at p15) (const (2 : ℝ))

/-- `1|rj;prec|ΣwjCj`: has a polynomial time 3-approximation, by solving a linear program (LP) and doing list scheduling in order of completion times in the LP solution.

Andreas S. Schulz (1996). Scheduling to minimize total weighted completion time: Performance guarantees of LP-based heuristics and lower bounds. https://doi.org/10.1007/3-540-61310-2_23
-/
def p16_r0 (R : Reading F) : Prop :=
  Approx (R.at p16) (const (3 : ℝ))

/-- `1|rj;prec|ΣwjCj`: has a polynomial time sqrt e/(sqrt e-1)-approximation.

Martin Skutella (2017). A 2.542-Approximation for Precedence Constrained Single Machine Scheduling with Release Dates and Total Weighted Completion Time Objective. https://doi.org/10.1016/j.orl.2016.07.016
-/
def p16_r1 (R : Reading F) : Prop :=
  Approx (R.at p16) (const ((Real.sqrt (Real.exp 1)) / ((Real.sqrt (Real.exp 1)) - 1)))

/-- `1|rj;prec|ΣwjCj`: randomized approximation ratio using alpha-points ≤e+epsilon.

Skutella, Martin (2006). List scheduling in order of $\alpha$-points on a single machine. https://doi.org/10.1007/11671541_9
-/
def p16_r2 (R : Reading F) : Prop :=
  ∀ ε : ℚ, 0 < ε → RandomApprox (R.at p16) (const ((Real.exp 1) + ε))

/-- `1|rj;prec|ΣwjCj`: has a polynomial-time (2+epsilon)-approximation.

René Sitters and Liya Yang (2018). A $(2 + \epsilon)$-approximation for precedence constrained single machine scheduling with release dates and total weighted completion time objective. https://doi.org/10.1016/j.orl.2018.05.007
-/
def p16_r3 (R : Reading F) : Prop :=
  ∀ ε : ℚ, 0 < ε → Approx (R.at p16) (const (2 + ε))

/-- `P|prec;pj=1|Cmax`: is W[2]-hard with respect to the number m of machines.

Bodlaender, Hans L and Fellows, Michael R (1995). W[2]-hardness of precedence constrained k-processor scheduling. https://doi.org/10.1016/0167-6377(95)00031-9
-/
def p17_r0 (R : Reading F) : Prop :=
  WHard (R.at p17) 2 (lift (Ops.m p17))

/-- `P|prec;pj=1|Cmax`: polynomial time approximation ratio ≥4/3.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22

Note: read as holding unless P = NP.
-/
def p17_r1 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p17) ((4 : ℝ) / 3)

/-- `P|prec;pj=1|Cmax`: is strongly NP-hard.

Ullman, J.D. (1975). NP-complete scheduling problems. https://doi.org/10.1016/s0022-0000(75)80008-0
-/
def p17_r2 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p17)

/-- `P2|prec;pj∈1,2|Cmax`: is W[2]-hard with respect to the width of the partial order.

van Bevern, René and Bredereck, Robert and Bulteau, Laurent and Komusiewicz, Christian and Talmon, Nimrod and Woeginger, Gerhard J (2016). Precedence-constrained scheduling problems parameterized by partial order width. https://doi.org/10.1007/978-3-319-44914-2_9
-/
def p18_r0 (R : Reading F) : Prop :=
  WHard (R.at p18) 2 (lift (Ops.width p18))

/-- `P2|prec;pj∈1,2|Cmax`: is strongly NP-hard.

Ullman, J.D. (1975). NP-complete scheduling problems. https://doi.org/10.1016/s0022-0000(75)80008-0
-/
def p18_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p18)

/-- `1|rj|ΣwjCj`: randomized approximation ratio using alpha-points ≤1.6853.

Skutella, Martin (2006). List scheduling in order of $\alpha$-points on a single machine. https://doi.org/10.1007/11671541_9
-/
def p19_r1 (R : Reading F) : Prop :=
  RandomApprox (R.at p19) (const (1.6853 : ℝ))

/-- `1|rj|ΣwjCj`: randomized approximation ratio ≤1.6853 in time O(nlog n).

Schulz, Andreas S and Skutella, Martin (1997). Scheduling-LPs bear probabilities randomized approximations for min-sum criteria. https://doi.org/10.1007/3-540-63397-9_32
-/
def p19_r3 (R : Reading F) : Prop :=
  RandomApproxWithin (R.at p19) (const 1.6853) (fun x => (Ops.n p19 x) * Nat.log 2 (Ops.n p19 x))

/-- `1|rj|ΣwjCj`: deterministic approximation ratio ≤2 in time O(n^2).

Goemans, Michel X (1997). Improved approximation algorthims for scheduling with release dates. None
-/
def p19_r4 (R : Reading F) : Prop :=
  ApproxWithin (R.at p19) (const 2) (fun x => (Ops.n p19 x) ^ 2)

/-- `1|rj|ΣwjCj`: deterministic approximation ratio ≤2.

Han Hoogeveen and Arjen P. A. Vestjens (1996). Optimal On-Line Algorithms for Single-Machine Scheduling. https://doi.org/10.1007/3-540-61310-2_30
-/
def p19_r5 (R : Reading F) : Prop :=
  Approx (R.at p19) (const (2 : ℝ))

/-- `1|rj|ΣwjCj`: randomized approximation ratio ≤e/(e-1) approx 1.58 by algorithm BEST-alpha.

Chekuri, Chandra and Motwani, Rajeev and Natarajan, Balas and Stein, Clifford (2001). Approximation techniques for average completion time scheduling. https://doi.org/10.1137/s0097539797327180
-/
def p19_r6 (R : Reading F) : Prop :=
  RandomApprox (R.at p19) (const ((Real.exp 1) / ((Real.exp 1) - 1)))

/-- `1|rj|ΣwjCj`: randomized (oblivious model) competitive ratio ≤e/(e-1) approx 1.58 by algorithm BEST-alpha.

Chekuri, Chandra and Motwani, Rajeev and Natarajan, Balas and Stein, Clifford (2001). Approximation techniques for average completion time scheduling. https://doi.org/10.1137/s0097539797327180
-/
def p19_r7 (R : Reading F) : Prop :=
  RandCompetitive (R.at p19) (const ((Real.exp 1) / ((Real.exp 1) - 1)))

/-- `1|pj=p;rj|ΣwjCj`: is in P.

Baptiste, P. (2000). Scheduling equal-length jobs on identical parallel machines. https://doi.org/10.1016/s0166-218x(99)00238-3
-/
def p20_r0 (R : Reading F) : Prop :=
  InP (R.at p20)

/-- `1|pj=p;rj|ΣTj`: is in P.

Baptiste, P. (2000). Scheduling equal-length jobs on identical parallel machines. https://doi.org/10.1016/s0166-218x(99)00238-3
-/
def p21_r0 (R : Reading F) : Prop :=
  InP (R.at p21)

/-- `P|pj=p;rj|ΣwjCj`: is in P.

Brucker, P. and Kravchenko, S.A. (2008). Scheduling jobs with equal processing times and time windows on identical parallel machines. https://doi.org/10.1007/s10951-008-0063-y
-/
def p22_r0 (R : Reading F) : Prop :=
  InP (R.at p22)

/-- `P|pj=p;rj|ΣwjCj`, parameter m: is in P.

Baptiste, P. (2000). Scheduling equal-length jobs on identical parallel machines. https://doi.org/10.1016/s0166-218x(99)00238-3

Note: in P for every fixed value.
-/
def p22_r1 (R : Reading F) : Prop :=
  InPFixed (R.at p22) (lift (Ops.m p22))

/-- `P|pj=p;rj|ΣTj`: is in P.

Brucker, P. and Kravchenko, S.A. (2005). Scheduling jobs with release times on parallel machines to minimize total tardiness. None
-/
def p23_r0 (R : Reading F) : Prop :=
  InP (R.at p23)

/-- `P|pj=p;rj|ΣTj`, parameter m: is in P.

Baptiste, P. (2000). Scheduling equal-length jobs on identical parallel machines. https://doi.org/10.1016/s0166-218x(99)00238-3

Note: in P for every fixed value.
-/
def p23_r1 (R : Reading F) : Prop :=
  InPFixed (R.at p23) (lift (Ops.m p23))

/-- `P|rj;pj=p;sizej|Cmax`, parameter m: is in P.

Baptiste, P. (2003). A note on scheduling multiprocessor tasks with identical processing times. https://doi.org/10.1016/s0305-0548(02)00116-8

Note: in P for every fixed value.
-/
def p24_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p24) (lift (Ops.m p24))

/-- `P|rj;pj=p;sizej|ΣCj`, parameter m: is in P.

Baptiste, P. (2003). A note on scheduling multiprocessor tasks with identical processing times. https://doi.org/10.1016/s0305-0548(02)00116-8

Note: in P for every fixed value.
-/
def p25_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p25) (lift (Ops.m p25))

/-- `1|pj=p;rj|ΣwjUj`: is in P.

Baptiste, P. (1999). Polynomial time algorithms for minimizing the weighted number of late jobs on a single machine with equal processing times. https://doi.org/10.1002/(sici)1099-1425(199911/12)2:6<245::aid-jos28>3.0.co;2-5
-/
def p26_r0 (R : Reading F) : Prop :=
  InP (R.at p26)

/-- `P|pj=p;intree|ΣCj`, parameter m: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None

Note: in P for every fixed value.
-/
def p27_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p27) (lift (Ops.m p27))

/-- `P|pj=p;tree|ΣCj`, parameter m: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None

Note: in P for every fixed value.
-/
def p28_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p28) (lift (Ops.m p28))

/-- `P|rj;pj=p|ΣwjUj`, parameter pmax: is in P.

Heeger,Klaus and Molter,Hendrik (2024). Minimizing the Number of Tardy Jobs with Uniform Processing Times on Parallel Machines. https://arxiv.org/abs/2404.14208

Note: in P for every fixed value.
-/
def p29_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p29) (lift (Ops.pmax p29))

/-- `P|rj;pj=p|ΣwjUj`, parameter m+pmax: is fixed parameter tractable.

Heeger,Klaus and Molter,Hendrik (2024). Minimizing the Number of Tardy Jobs with Uniform Processing Times on Parallel Machines. https://arxiv.org/abs/2404.14208
-/
def p29_r1 (R : Reading F) : Prop :=
  IsFPT (R.at p29) (tplus (lift (Ops.m p29)) (lift (Ops.pmax p29)))

/-- `P|rj;pj=p|ΣwjUj`, parameter #r: is fixed parameter tractable.

Heeger,Klaus and Molter,Hendrik (2024). Minimizing the Number of Tardy Jobs with Uniform Processing Times on Parallel Machines. https://arxiv.org/abs/2404.14208
-/
def p29_r2 (R : Reading F) : Prop :=
  IsFPT (R.at p29) (lift (Ops.numR p29))

/-- `P|rj;pj=p|ΣwjUj`, parameter #d: is fixed parameter tractable.

Heeger,Klaus and Molter,Hendrik (2024). Minimizing the Number of Tardy Jobs with Uniform Processing Times on Parallel Machines. https://arxiv.org/abs/2404.14208
-/
def p29_r3 (R : Reading F) : Prop :=
  IsFPT (R.at p29) (lift (Ops.numD p29))

/-- `P|rj;pj=p|ΣwjUj`, parameter m: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None

Note: in P for every fixed value.
-/
def p29_r4 (R : Reading F) : Prop :=
  InPFixed (R.at p29) (lift (Ops.m p29))

/-- `P|pj=1;chains;rj|Lmax`: is in P.

Baptiste, P. and Brucker, P. and Knust, S. and Timkovsky, V. (2004). Ten notes on equal-execution-time scheduling. None
-/
def p30_r0 (R : Reading F) : Prop :=
  InP (R.at p30)

/-- `P|pj=1;chains;rj|Lmax`: is in P.

Dror, M. and Kubiak, W. and Dell' Olmo, P. (1998). Strong-weak chain constrained scheduling. None
-/
def p30_r1 (R : Reading F) : Prop :=
  InP (R.at p30)

/-- `R||ΣCj`: is in P.

Bruno, J. and Coffman, Jr., E.G. and Sethi, R. (1974). Scheduling independent tasks to reduce mean finishing time. https://doi.org/10.1145/361011.361064
-/
def p31_r0 (R : Reading F) : Prop :=
  InP (R.at p31)

/-- `R||ΣCj`: is in P.

Horn, W.A. (1973). Minimizing average flow time with parallel machines. https://doi.org/10.1287/opre.21.3.846
-/
def p31_r1 (R : Reading F) : Prop :=
  InP (R.at p31)

/-- `P2||ΣwjCj`: is NP-hard.

Bruno, J. and Coffman, Jr., E.G. and Sethi, R. (1974). Scheduling independent tasks to reduce mean finishing time. https://doi.org/10.1145/361011.361064
-/
def p32_r0 (R : Reading F) : Prop :=
  NPHard (R.at p32)

/-- `Q|Mj|ΣCj`: is in P.

Bruno, J. and Coffman, Jr., E.G. and Sethi, R. (1974). Scheduling independent tasks to reduce mean finishing time. https://doi.org/10.1145/361011.361064
-/
def p33_r0 (R : Reading F) : Prop :=
  InP (R.at p33)

/-- `Q|Mj|ΣCj`: is in P.

Horn, W.A. (1973). Minimizing average flow time with parallel machines. https://doi.org/10.1287/opre.21.3.846
-/
def p33_r1 (R : Reading F) : Prop :=
  InP (R.at p33)

/-- `P2|Mj|ΣwjCj`: is NP-hard.

Bruno, J. and Coffman, Jr., E.G. and Sethi, R. (1974). Scheduling independent tasks to reduce mean finishing time. https://doi.org/10.1145/361011.361064
-/
def p34_r0 (R : Reading F) : Prop :=
  NPHard (R.at p34)

/-- `P;S1|sj=s;pj=p;rj|Cmax`: is in P.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p35_r0 (R : Reading F) : Prop :=
  InP (R.at p35)

/-- `P;S1|sj=s;pj=p;rj|ΣCj`: is in P.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p36_r0 (R : Reading F) : Prop :=
  InP (R.at p36)

/-- `P;S1|sj=s;pj=1;rj|ΣwjCj`: is in P.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p37_r0 (R : Reading F) : Prop :=
  InP (R.at p37)

/-- `P;S1|sj=s;pj=1;rj|ΣwjUj`: is in P.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p38_r0 (R : Reading F) : Prop :=
  InP (R.at p38)

/-- `P;S1|sj=s;pj=1;rj|ΣTj`: is in P.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p39_r0 (R : Reading F) : Prop :=
  InP (R.at p39)

/-- `P2;S1|pj=p|Cmax`: is NP-hard.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p40_r0 (R : Reading F) : Prop :=
  NPHard (R.at p40)

/-- `P2;S1|pj=p|ΣCj`: is NP-hard.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p41_r0 (R : Reading F) : Prop :=
  NPHard (R.at p41)

/-- `P2;S1|pj=1;rj|Lmax`: is strongly NP-hard.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p42_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p42)

/-- `P2;S1|pj=1;rj|Lmax`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p42_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p42)

/-- `P2;S1|pj=1;rj|ΣCj`: is strongly NP-hard.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p43_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p43)

/-- `P2;S1|pj=1;rj|ΣCj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p43_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p43)

/-- `P;S1|sj=1|ΣCj`: is strongly NP-hard.

Brucker, P. and Dhaenens-Flipo, C. and Knust, S. and Kravchenko, S.A. and Werner, F. (2002). Complexity results for parallel machine problems with a single server. https://doi.org/10.1002/jos.120
-/
def p44_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p44)

/-- `P3|fixj|Cmax`: is strongly NP-hard.

Błażewicz, J. and Dell' Olmo, P. and Drozdowski, M. and Speranza, M.G. (1992). Scheduling multiprocessor tasks on three dedicated processors. https://doi.org/10.1016/0020-0190(92)90172-r
-/
def p45_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p45)

/-- `P3|fixj|Cmax`: is strongly NP-hard.

Błażewicz, J. and Dell' Olmo, P. and Drozdowski, M. and Speranza, M.G. (1994). Corrigendum to: Scheduling multiprocessor tasks on three dedicated processors. None
-/
def p45_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p45)

/-- `P3|fixj|Cmax`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p45_r2 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p45)

/-- `P|pj=p;sizej|Cmax`, parameter m: is in P.

Błażewicz, J. and Drabowski, M. and Wȩglarz, J. (1986). Scheduling multiprocessor tasks to minimize schedule length. https://doi.org/10.1109/tc.1986.1676781

Note: in P for every fixed value.
-/
def p46_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p46) (lift (Ops.m p46))

/-- `P|pj=p;outtree;rj|Cmax`: is in P.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p47_r0 (R : Reading F) : Prop :=
  InP (R.at p47)

/-- `P|pj=p;intree|Lmax`: is in P.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p48_r0 (R : Reading F) : Prop :=
  InP (R.at p48)

/-- `P|pj=1;intree;rj|Cmax`: is strongly NP-hard.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p49_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p49)

/-- `P|pj=1;outtree|Lmax`: is strongly NP-hard.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p50_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p50)

/-- `P|Mj;intree;pj=1;rj|Cmax`: is strongly NP-hard.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p51_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p51)

/-- `P|Mj;outtree;pj=1|Lmax`: is strongly NP-hard.

Brucker, P. and Garey, M.R. and Johnson, D.S. (1977). Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness. https://doi.org/10.1287/moor.2.3.275
-/
def p52_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p52)

/-- `P|pj=1;outtree;rj|ΣCj`: is in P.

Brucker, P. and Hurink, J. and Knust, S. (2002). A polynomial algorithm for $P|p_j=1, r_j, outtree|\sumC_j$. None
-/
def p53_r0 (R : Reading F) : Prop :=
  InP (R.at p53)

/-- `P|pj=1;outtree;rj|ΣCj`: is in P.

Huo, Y. and Leung, J.Y.-T. (2005). Minimizing total completion time for UET tasks with release time and outtree precedence constraints. https://doi.org/10.1007/s00186-005-0009-5
-/
def p53_r1 (R : Reading F) : Prop :=
  InP (R.at p53)

/-- `Q2|pj=1;chains|Cmax`: is in P.

Brucker, P. and Hurink, J. and Kubiak, W. (1999). Scheduling identical jobs with chain precedence constraints on two uniform machines. https://doi.org/10.1007/pl00020913
-/
def p54_r0 (R : Reading F) : Prop :=
  InP (R.at p54)

/-- `P|Mj;pj=1;rj|ΣwjUj`: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030
-/
def p55_r0 (R : Reading F) : Prop :=
  InP (R.at p55)

/-- `Q|Mj;pj=1|ΣwjUj`: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030
-/
def p56_r0 (R : Reading F) : Prop :=
  InP (R.at p56)

/-- `P|Mj;pj=1;rj|ΣwjTj`: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030
-/
def p57_r0 (R : Reading F) : Prop :=
  InP (R.at p57)

/-- `Q|Mj;pj=1|ΣwjTj`: is in P.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030
-/
def p58_r0 (R : Reading F) : Prop :=
  InP (R.at p58)

/-- `P2|Mj;chains;pj=1|Cmax`: is NP-hard.

Brucker, P. and Jurisch, B. and Krämer, A. (1997). Complexity of scheduling problems with multi-purpose machines. https://doi.org/10.1023/a:1018950911030
-/
def p59_r0 (R : Reading F) : Prop :=
  NPHard (R.at p59)

/-- `1|outtree;l;pj=1;rj|Cmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p60_r0 (R : Reading F) : Prop :=
  InP (R.at p60)

/-- `1|tree;l;pj=1|Cmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p61_r0 (R : Reading F) : Prop :=
  InP (R.at p61)

/-- `1|intree;l;pj=1|Lmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p62_r0 (R : Reading F) : Prop :=
  InP (R.at p62)

/-- `1|prec;l=1;pj=1;rj|Lmax`: is in P.

Bruno, J. and Jones, III, J.W. and So, K. (1980). Deterministic scheduling with pipelined processors. https://doi.org/10.1109/tc.1980.1675569
-/
def p63_r0 (R : Reading F) : Prop :=
  InP (R.at p63)

/-- `P|fixj;rj;pj=1|Cmax`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p64_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p64) (lift (Ops.m p64))

/-- `P|fixj;rj;pj=1|ΣCj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p65_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p65) (lift (Ops.m p65))

/-- `P|fixj;pj=1|ΣwjCj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p66_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p66) (lift (Ops.m p66))

/-- `P|fixj;pj=1|ΣwjUj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p67_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p67) (lift (Ops.m p67))

/-- `P|fixj;pj=1|ΣTj`, parameter m: is in P.

Brucker, P. and Krämer, A. (1996). Polynomial Algorithms for resource-constrained and multiprocessor task scheduling problems. https://doi.org/10.1016/0377-2217(95)00350-9

Note: in P for every fixed value.
-/
def p68_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p68) (lift (Ops.m p68))

/-- `1|outtree;l;pj=1;rj|ΣCj`: is in P.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p69_r0 (R : Reading F) : Prop :=
  InP (R.at p69)

/-- `1|prec;l=1;pj=1|ΣCj`: is in P.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p70_r0 (R : Reading F) : Prop :=
  InP (R.at p70)

/-- `1|intree;l;pj=1;rj|Cmax`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p71_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p71)

/-- `1|outtree;l;pj=1|Lmax`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p72_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p72)

/-- `1|chains;l|ΣCj`: is strongly NP-hard.

Brucker, P. and Knust, S. (1999). Complexity results for single-machine problems with positive finish-start time-lags. https://doi.org/10.1007/s006070050036
-/
def p73_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p73)

/-- `1|chains;l;pj=p|ΣCj`: is in P.

Brucker, P. and Knust, S. and Oguz, C. (2006). Scheduling chains with identical jobs and constant delays on a single machine. https://doi.org/10.1007/s00186-005-0014-8
-/
def p74_r0 (R : Reading F) : Prop :=
  InP (R.at p74)

/-- `P2|rj;pj=1;sizej|ΣCj`: is in P.

Brucker, P. and Knust, S. and Roper, D. and Zinder, Y. (2000). Scheduling UET task systems with concurrency on two parallel identical processors. https://doi.org/10.1007/s001860000089
-/
def p75_r0 (R : Reading F) : Prop :=
  InP (R.at p75)

/-- `P|pj=p;sizej|ΣwjUj`, parameter m: is in P.

Brucker, P. and Knust, S. and Roper, D. and Zinder, Y. (2000). Scheduling UET task systems with concurrency on two parallel identical processors. https://doi.org/10.1007/s001860000089

Note: in P for every fixed value.
-/
def p76_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p76) (lift (Ops.m p76))

/-- `P|pj=p;sizej|ΣTj`, parameter m: is in P.

Brucker, P. and Knust, S. and Roper, D. and Zinder, Y. (2000). Scheduling UET task systems with concurrency on two parallel identical processors. https://doi.org/10.1007/s001860000089

Note: in P for every fixed value.
-/
def p77_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p77) (lift (Ops.m p77))

/-- `P2|chains;rj;pj=1;sizej|Cmax`: is strongly NP-hard.

Brucker, P. and Knust, S. and Roper, D. and Zinder, Y. (2000). Scheduling UET task systems with concurrency on two parallel identical processors. https://doi.org/10.1007/s001860000089
-/
def p78_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p78)

/-- `P2|chains;pj=1;sizej|Lmax`: is strongly NP-hard.

Brucker, P. and Knust, S. and Roper, D. and Zinder, Y. (2000). Scheduling UET task systems with concurrency on two parallel identical processors. https://doi.org/10.1007/s001860000089
-/
def p79_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p79)

/-- `P2|prec;pj=1;sizej|ΣCj`: is strongly NP-hard.

Brucker, P. and Knust, S. and Roper, D. and Zinder, Y. (2000). Scheduling UET task systems with concurrency on two parallel identical processors. https://doi.org/10.1007/s001860000089
-/
def p80_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p80)

/-- `P|chains;pj=1;sizej|Cmax`, parameter m: is strongly NP-hard.

Błażewicz, J. and Liu, Z. (1996). Scheduling multiprocessor tasks with chain constraints. https://doi.org/10.1016/0377-2217(96)00126-9
-/
def p81_r0 (R : Reading F) : Prop :=
  StronglyParaNPHard (R.at p81) (lift (Ops.m p81))

/-- `P3|chains;pj=1;sizej|Cmax`: is strongly NP-hard.

Błażewicz, J. and Liu, Z. (1996). Scheduling multiprocessor tasks with chain constraints. https://doi.org/10.1016/0377-2217(96)00126-9
-/
def p82_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p82)

/-- `P2|fixj;chains;pj=1|Cmax`: is strongly NP-hard.

Błażewicz, J. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1983). Scheduling subject to resource constraints: classification and complexity. https://doi.org/10.1016/0166-218x(83)90012-4
-/
def p83_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p83)

/-- `P2|fixj;chains;pj=1|Cmax`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p83_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p83)

/-- `P2|fixj;chains;pj=1|ΣCj`: is strongly NP-hard.

Błażewicz, J. and Lenstra, J.K. and Rinnooy Kan, A.H.G. (1983). Scheduling subject to resource constraints: classification and complexity. https://doi.org/10.1016/0166-218x(83)90012-4
-/
def p84_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p84)

/-- `P2|fixj;chains;pj=1|ΣCj`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p84_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p84)

/-- `P2|pj=1;prec;rj|ΣCj`: is in P.

Baptiste, P. and Timkovsky, V. (2004). Shortest path to nonpreemptive schedules of unit-time jobs on two identical parallel machines with minimum total completion time. https://doi.org/10.1007/s001860300336
-/
def p85_r0 (R : Reading F) : Prop :=
  InP (R.at p85)

/-- `1|prec;l=1;pj=1;rj|ΣCj`: is in P.

Baptiste, P. and Timkovsky, V. (2004). Shortest path to nonpreemptive schedules of unit-time jobs on two identical parallel machines with minimum total completion time. https://doi.org/10.1007/s001860300336
-/
def p86_r0 (R : Reading F) : Prop :=
  InP (R.at p86)

/-- `P2|pj=p;prec|Cmax`: is in P.

Coffman, Jr., E.G. and Graham, R.L. (1971/1972). Optimal scheduling for two-processor systems. https://doi.org/10.1007/bf00288685
-/
def p87_r0 (R : Reading F) : Prop :=
  InP (R.at p87)

/-- `P2|pj=p;prec|Cmax`: is in P.

Gabow, H.N. (1982). An almost-linear algorithm for two-processor scheduling. https://doi.org/10.1145/322326.322335
-/
def p87_r1 (R : Reading F) : Prop :=
  InP (R.at p87)

/-- `P2|pj=p;prec|Cmax`: is in P.

Sethi, R. (1976). Scheduling graphs on two processors. https://doi.org/10.1137/0205005
-/
def p87_r2 (R : Reading F) : Prop :=
  InP (R.at p87)

/-- `P2|pj=p;prec|ΣCj`: is in P.

Coffman, Jr., E.G. and Graham, R.L. (1971/1972). Optimal scheduling for two-processor systems. https://doi.org/10.1007/bf00288685
-/
def p88_r0 (R : Reading F) : Prop :=
  InP (R.at p88)

/-- `P2|fixj|ΣCj`: is strongly NP-hard.

Cai, X. and Lee, C.-Y. and Li, C.-L. (1998). Minimizing total completion time in two-processor task systems with prespecified processor allocations. https://doi.org/10.1002/(sici)1520-6750(199803)45:2<231::aid-nav7>3.3.co;2-0
-/
def p89_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p89)

/-- `P2|fixj|ΣCj`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p89_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p89)

/-- `P|pj=p;tree|Cmax`: is in P.

Davida, G.I. and Linton, D.J. (1976). A new algorithm for the scheduling of tree structured tasks. None
-/
def p90_r0 (R : Reading F) : Prop :=
  InP (R.at p90)

/-- `P|pj=p;tree|Cmax`: is in P.

Hu, T.C. (1961). Parallel sequencing and assembly line problems. https://doi.org/10.1287/opre.9.6.841
-/
def p90_r1 (R : Reading F) : Prop :=
  InP (R.at p90)

/-- `P|pj=p;sizej|ΣwjCj`, parameter m: is in P.

Drozdowski, M. and Dell' Olmo, P. (2000). Scheduling multiprocessor tasks for mean flow time criterion. https://doi.org/10.1016/s0305-0548(99)00048-9

Note: in P for every fixed value.
-/
def p91_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p91) (lift (Ops.m p91))

/-- `P|pj=1;sizej|ΣCj`: is strongly NP-hard.

Drozdowski, M. and Dell' Olmo, P. (2000). Scheduling multiprocessor tasks for mean flow time criterion. https://doi.org/10.1016/s0305-0548(99)00048-9
-/
def p92_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p92)

/-- `P2|sizej|Cmax`: is in Ppseudo.

Du, J. and Leung, J.Y.-T. (1989). Complexity of scheduling parallel task systems. https://doi.org/10.1137/0402042
-/
def p93_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p93)

/-- `P3|sizej|Cmax`: is in Ppseudo.

Du, J. and Leung, J.Y.-T. (1989). Complexity of scheduling parallel task systems. https://doi.org/10.1137/0402042
-/
def p94_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p94)

/-- `P5|sizej|Cmax`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. (1989). Complexity of scheduling parallel task systems. https://doi.org/10.1137/0402042
-/
def p95_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p95)

/-- `P|sizej|Cmax`, parameter m: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. (1989). Complexity of scheduling parallel task systems. https://doi.org/10.1137/0402042
-/
def p96_r0 (R : Reading F) : Prop :=
  StronglyParaNPHard (R.at p96) (lift (Ops.m p96))

/-- `1||ΣTj`: is in Ppseudo.

Du, J. and Leung, J.Y.-T. (1990). Minimizing total tardiness on one machine is NP-hard. https://doi.org/10.1287/moor.15.3.483
-/
def p97_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p97)

/-- `1||ΣTj`: is NP-hard.

Du, J. and Leung, J.Y.-T. (1990). Minimizing total tardiness on one machine is NP-hard. https://doi.org/10.1287/moor.15.3.483
-/
def p97_r1 (R : Reading F) : Prop :=
  NPHard (R.at p97)

/-- `1||ΣTj`: is in Ppseudo.

Lawler, E.L. (1977). A pseudopolynomial algorithm for sequencing jobs to minimize total tardiness. https://doi.org/10.1016/s0167-5060(08)70742-8
-/
def p97_r2 (R : Reading F) : Prop :=
  PseudoPoly (R.at p97)

/-- `1||ΣTj`: is NP-hard.

Lawler, E.L. (1977). A pseudopolynomial algorithm for sequencing jobs to minimize total tardiness. https://doi.org/10.1016/s0167-5060(08)70742-8
-/
def p97_r3 (R : Reading F) : Prop :=
  NPHard (R.at p97)

/-- `Q|pj=1;rj|ΣCj`, parameter m: is in P.

Dessouky, M.I. and Lageweg, B.J. and Lenstra, J.K. and van de Velde, S.L. (1990). Scheduling identical jobs on uniform parallel machines. https://doi.org/10.1111/j.1467-9574.1990.tb01276.x

Note: in P for every fixed value.
-/
def p98_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p98) (lift (Ops.m p98))

/-- `Q|pj=p;rj|ΣCj`, parameter m: is in P.

Dessouky, M.I. and Lageweg, B.J. and Lenstra, J.K. and van de Velde, S.L. (1990). Scheduling identical jobs on uniform parallel machines. https://doi.org/10.1111/j.1467-9574.1990.tb01276.x

Note: in P for every fixed value.
-/
def p99_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p99) (lift (Ops.m p99))

/-- `P2|chains|Cmax`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1991). Scheduling chain-structured tasks to minimize makespan and mean flow time. https://doi.org/10.1016/0890-5401(91)90009-q
-/
def p100_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p100)

/-- `P2|chains|ΣCj`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1991). Scheduling chain-structured tasks to minimize makespan and mean flow time. https://doi.org/10.1016/0890-5401(91)90009-q
-/
def p101_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p101)

/-- `P2|Mj;chains|Cmax`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1991). Scheduling chain-structured tasks to minimize makespan and mean flow time. https://doi.org/10.1016/0890-5401(91)90009-q
-/
def p102_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p102)

/-- `P2|Mj;chains|ΣCj`: is strongly NP-hard.

Du, J. and Leung, J.Y.-T. and Young, G.H. (1991). Scheduling chain-structured tasks to minimize makespan and mean flow time. https://doi.org/10.1016/0890-5401(91)90009-q
-/
def p103_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p103)

/-- `1|prec;l=1|Cmax`: is in P.

Finta, L. and Liu, Z. (1996). Single machine scheduling subject to precedence delays. https://doi.org/10.1016/0166-218x(96)00110-2
-/
def p104_r0 (R : Reading F) : Prop :=
  InP (R.at p104)

/-- `P2|pj=p;prec|Lmax`: is in P.

Garey, M.R. and Johnson, D.S. (1976). Scheduling tasks with nonuniform deadlines on two processors. https://doi.org/10.1145/321958.321967
-/
def p105_r0 (R : Reading F) : Prop :=
  InP (R.at p105)

/-- `P2|pj=1;prec;rj|Lmax`: is in P.

Garey, M.R. and Johnson, D.S. (1977). Two-processor scheduling with start-times and deadlines. https://doi.org/10.1137/0206029
-/
def p106_r0 (R : Reading F) : Prop :=
  InP (R.at p106)

/-- `P|Mj|Cmax`: is strongly NP-hard.

Garey, M.R. and Johnson, D.S. (1978). Strong NP-completeness results: motivation, examples, and implications. https://doi.org/10.1145/322077.322090
-/
def p107_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p107)

/-- `P|pj=p;outtree|ΣCj`: is in P.

Hu, T.C. (1961). Parallel sequencing and assembly line problems. https://doi.org/10.1287/opre.9.6.841
-/
def p108_r0 (R : Reading F) : Prop :=
  InP (R.at p108)

/-- `P2;S1|sj=1|ΣCj`: is in P.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p109_r0 (R : Reading F) : Prop :=
  InP (R.at p109)

/-- `P;S1|pj=1|ΣwjCj`: is in P.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p110_r0 (R : Reading F) : Prop :=
  InP (R.at p110)

/-- `P;S1|pj=1|ΣUj`: is in P.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p111_r0 (R : Reading F) : Prop :=
  InP (R.at p111)

/-- `P2;S1|sj=1|Cmax`: is in Ppseudo.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p112_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p112)

/-- `P2;S1|sj=1|Cmax`: is in Ppseudo.

Kravchenko, S.A. and Werner, F. (1997). Parallel machine scheduling problems with a single server. https://doi.org/10.1016/s0895-7177(97)00236-7
-/
def p112_r1 (R : Reading F) : Prop :=
  PseudoPoly (R.at p112)

/-- `P2;S1|pj=1|ΣwjUj`: is in Ppseudo.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p113_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p113)

/-- `P2;S1|pj=1|ΣwjUj`: is NP-hard.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p113_r1 (R : Reading F) : Prop :=
  NPHard (R.at p113)

/-- `P2;S1|pj=1|ΣwjUj`: is in Ppseudo.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p113_r2 (R : Reading F) : Prop :=
  PseudoPoly (R.at p113)

/-- `P2;S1|pj=1|ΣwjUj`: is NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p113_r3 (R : Reading F) : Prop :=
  NPHard (R.at p113)

/-- `P2;S1|pj=1|ΣTj`: is in Ppseudo.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p114_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p114)

/-- `P2;S1|pj=1|ΣTj`: is NP-hard.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p114_r1 (R : Reading F) : Prop :=
  NPHard (R.at p114)

/-- `P2;S1|pj=1|ΣTj`: is in Ppseudo.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p114_r2 (R : Reading F) : Prop :=
  PseudoPoly (R.at p114)

/-- `P2;S1|pj=1|ΣTj`: is NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p114_r3 (R : Reading F) : Prop :=
  NPHard (R.at p114)

/-- `P2;S1|sj=s|Cmax`: is strongly NP-hard.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p115_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p115)

/-- `P2;S1|sj=1|Lmax`: is strongly NP-hard.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p116_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p116)

/-- `P2;S1|sj=s|ΣCj`: is strongly NP-hard.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p117_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p117)

/-- `P2;S1|pj=1|ΣwjTj`: is strongly NP-hard.

Hall, N. and Potts, C.N. and Sriskandarajah, C. (2000). Parallel machine scheduling with a common server. https://doi.org/10.1016/s0166-218x(99)00206-1
-/
def p118_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p118)

/-- `P2;S1|pj=1|ΣwjTj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p118_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p118)

/-- `P2|fixj|Cmax`: is in P.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p119_r0 (R : Reading F) : Prop :=
  InP (R.at p119)

/-- `P|fixj;pj=1|Cmax`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p120_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p120)

/-- `P2|fixj;rj|Cmax`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p121_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p121)

/-- `P2|fixj|Lmax`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p122_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p122)

/-- `P|fixj;pj=1|ΣCj`: is strongly NP-hard.

Hoogeveen, J.A. and van de Velde, S.L. and Veltman, B. (1994). Complexity of scheduling multiprocessor tasks with prespecified processor allocations. https://doi.org/10.1016/0166-218x(94)90012-4
-/
def p123_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p123)

/-- `1||ΣwjUj`: is Ppseudo.

Karp, R.M. (1972). Reducibility among combinatorial problems. https://doi.org/10.1007/978-1-4684-2001-2_9
-/
def p124_r0 (R : Reading F) : Prop :=
  PseudoPoly (R.at p124)

/-- `1||ΣwjUj`: is NP-hard.

Karp, R.M. (1972). Reducibility among combinatorial problems. https://doi.org/10.1007/978-1-4684-2001-2_9
-/
def p124_r1 (R : Reading F) : Prop :=
  NPHard (R.at p124)

/-- `1||ΣwjUj`: is in Ppseudo.

Lawler, E.L. and Moore, J.M. (1969). A functional equation and its application to resource allocation and sequencing problems. https://doi.org/10.1287/mnsc.16.1.77
-/
def p124_r2 (R : Reading F) : Prop :=
  PseudoPoly (R.at p124)

/-- `1||ΣwjUj`: is NP-hard.

Lawler, E.L. and Moore, J.M. (1969). A functional equation and its application to resource allocation and sequencing problems. https://doi.org/10.1287/mnsc.16.1.77
-/
def p124_r3 (R : Reading F) : Prop :=
  NPHard (R.at p124)

/-- `1||ΣwjUj`, parameter #d+#p: is fixed parameter tractable.

Hermelin, Danny and Karhi, Shlomo and Pinedo, Michael and Shabtay, Dvir (2021). New algorithms for minimizing the weighted number of tardy jobs on a single machine. https://link.springer.com/article/10.1007/s10479-018-2852-9
-/
def p124_r4 (R : Reading F) : Prop :=
  IsFPT (R.at p124) (tplus (lift (Ops.numD p124)) (lift (Ops.numP p124)))

/-- `1||ΣwjUj`, parameter #d+#w: is fixed parameter tractable.

Hermelin, Danny and Karhi, Shlomo and Pinedo, Michael and Shabtay, Dvir (2021). New algorithms for minimizing the weighted number of tardy jobs on a single machine. https://link.springer.com/article/10.1007/s10479-018-2852-9
-/
def p124_r5 (R : Reading F) : Prop :=
  IsFPT (R.at p124) (tplus (lift (Ops.numD p124)) (lift (Ops.numW p124)))

/-- `1||ΣwjUj`, parameter #p+#w: is fixed parameter tractable.

Hermelin, Danny and Karhi, Shlomo and Pinedo, Michael and Shabtay, Dvir (2021). New algorithms for minimizing the weighted number of tardy jobs on a single machine. https://link.springer.com/article/10.1007/s10479-018-2852-9
-/
def p124_r6 (R : Reading F) : Prop :=
  IsFPT (R.at p124) (tplus (lift (Ops.numP p124)) (lift (Ops.numW p124)))

/-- `1||ΣwjUj`, parameter #p: is in P.

Hermelin, Danny and Karhi, Shlomo and Pinedo, Michael and Shabtay, Dvir (2021). New algorithms for minimizing the weighted number of tardy jobs on a single machine. https://link.springer.com/article/10.1007/s10479-018-2852-9

Note: in P for every fixed value.
-/
def p124_r7 (R : Reading F) : Prop :=
  InPFixed (R.at p124) (lift (Ops.numP p124))

/-- `1||ΣwjUj`, parameter #w: is in P.

Hermelin, Danny and Karhi, Shlomo and Pinedo, Michael and Shabtay, Dvir (2021). New algorithms for minimizing the weighted number of tardy jobs on a single machine. https://link.springer.com/article/10.1007/s10479-018-2852-9

Note: in P for every fixed value.
-/
def p124_r8 (R : Reading F) : Prop :=
  InPFixed (R.at p124) (lift (Ops.numW p124))

/-- `1||ΣwjUj`, parameter #p: is W[1]-hard.

Heeger, Klaus and Hermelin, Danny (2024). Minimizing the Weighted Number of Tardy Jobs is W[1]-hard. https://arxiv.org/abs/2401.01740
-/
def p124_r9 (R : Reading F) : Prop :=
  WHard (R.at p124) 1 (lift (Ops.numP p124))

/-- `P|fixj|Cmax`: is strongly NP-hard.

Kubale, M. (1987). The complexity of scheduling independent two-processor tasks on dedicated processors. https://doi.org/10.1016/0020-0190(87)90176-1
-/
def p125_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p125)

/-- `Q|pj=1;chains|Cmax`: is strongly NP-hard.

Kubiak, W. (1988). Exact and approximate algorithms for scheduling unit time tasks with tree-like precedence constraints. None
-/
def p126_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p126)

/-- `Q|pj=p;chains|Cmax`: is strongly NP-hard.

Kubiak, W. (1988). Exact and approximate algorithms for scheduling unit time tasks with tree-like precedence constraints. None
-/
def p127_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p127)

/-- `Q|Mj;chains;pj=1|Cmax`: is strongly NP-hard.

Kubiak, W. (1988). Exact and approximate algorithms for scheduling unit time tasks with tree-like precedence constraints. None
-/
def p128_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p128)

/-- `P|pj=1;intree;rj|ΣCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p129_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p129)

/-- `P|Mj|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. (unknown year). unknown title. None
-/
def p130_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p130)

/-- `1|prec;rj|Cmax`: is in P.

Lawler, E.L. (1973). Optimal sequencing of a single machine subject to precedence constraints. https://doi.org/10.1287/mnsc.19.5.544
-/
def p131_r0 (R : Reading F) : Prop :=
  InP (R.at p131)

/-- `1|prec|Lmax`: is in P.

Lawler, E.L. (1973). Optimal sequencing of a single machine subject to precedence constraints. https://doi.org/10.1287/mnsc.19.5.544
-/
def p132_r0 (R : Reading F) : Prop :=
  InP (R.at p132)

/-- `1||ΣwjTj`: is strongly NP-hard.

Lawler, E.L. (1977). A pseudopolynomial algorithm for sequencing jobs to minimize total tardiness. https://doi.org/10.1016/s0167-5060(08)70742-8
-/
def p133_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p133)

/-- `1||ΣwjTj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p133_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p133)

/-- `1|sp-graph|ΣwjCj`: is in P.

Lawler, E.L. (1978). Sequencing jobs to minimize total weighted completion time subject to precedence constraints. https://doi.org/10.1016/s0167-5060(08)70323-6
-/
def p134_r0 (R : Reading F) : Prop :=
  InP (R.at p134)

/-- `1|prec|ΣCj`: is strongly NP-hard.

Lawler, E.L. (1978). Sequencing jobs to minimize total weighted completion time subject to precedence constraints. https://doi.org/10.1016/s0167-5060(08)70323-6
-/
def p135_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p135)

/-- `1|prec|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p135_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p135)

/-- `1|bounded height;pj=1|ΣwjCj`: is strongly NP-hard.

Lawler, E.L. (1978). Sequencing jobs to minimize total weighted completion time subject to precedence constraints. https://doi.org/10.1016/s0167-5060(08)70323-6
-/
def p136_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p136)

/-- `P2|prec;pj=p;sizej|Cmax`: is in P.

Lloyd, E.L. (1981). Concurrent task systems. https://doi.org/10.1287/opre.29.1.189
-/
def p137_r0 (R : Reading F) : Prop :=
  InP (R.at p137)

/-- `P|pj=1;sizej|Cmax`: is strongly NP-hard.

Lloyd, E.L. (1981). Concurrent task systems. https://doi.org/10.1287/opre.29.1.189
-/
def p138_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p138)

/-- `P2|rj;pj=p;sizej|Cmax`: is in P.

Lee, C.-Y. and Cai, X. (1999). Scheduling one and two-processor tasks on two parallel processors. https://doi.org/10.1080/07408179908969847
-/
def p139_r0 (R : Reading F) : Prop :=
  InP (R.at p139)

/-- `P2|pj=p;sizej|ΣwjCj`: is in P.

Lee, C.-Y. and Cai, X. (1999). Scheduling one and two-processor tasks on two parallel processors. https://doi.org/10.1080/07408179908969847
-/
def p140_r0 (R : Reading F) : Prop :=
  InP (R.at p140)

/-- `P2|rj;sizej|Cmax`: is strongly NP-hard.

Lee, C.-Y. and Cai, X. (1999). Scheduling one and two-processor tasks on two parallel processors. https://doi.org/10.1080/07408179908969847
-/
def p141_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p141)

/-- `P2|sizej|Lmax`: is strongly NP-hard.

Lee, C.-Y. and Cai, X. (1999). Scheduling one and two-processor tasks on two parallel processors. https://doi.org/10.1080/07408179908969847
-/
def p142_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p142)

/-- `P2|sizej|ΣCj`: is NP-hard.

Lee, C.-Y. and Cai, X. (1999). Scheduling one and two-processor tasks on two parallel processors. https://doi.org/10.1080/07408179908969847
-/
def p143_r0 (R : Reading F) : Prop :=
  NPHard (R.at p143)

/-- `P2|sizej|ΣwjCj`: is strongly NP-hard.

Lee, C.-Y. and Cai, X. (1999). Scheduling one and two-processor tasks on two parallel processors. https://doi.org/10.1080/07408179908969847
-/
def p144_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p144)

/-- `Q|rj|Cmax`, parameter m: is in Ppseudo.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. and Shmoys, D.B. (1989). Sequencing and Scheduling: Algorithms and Complexity. None

Note: pseudo-polynomial for every fixed value.
-/
def p145_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p145) (lift (Ops.m p145))

/-- `Q||ΣwjCj`: has a polynomial-time approximation scheme.

Chekuri, Chandra and Khanna, Sanjeev (2001). A PTAS for Minimizing Weighted Completion Time on Uniformly Related Machines. https://doi.org/10.1007/3-540-48224-5_69
-/
def p146_r0 (R : Reading F) : Prop :=
  PTAS (R.at p146)

/-- `Q||ΣwjCj`, parameter m: is in Ppseudo.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. and Shmoys, D.B. (1989). Sequencing and Scheduling: Algorithms and Complexity. None

Note: pseudo-polynomial for every fixed value.
-/
def p146_r1 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p146) (lift (Ops.m p146))

/-- `Q||ΣwjUj`, parameter m: is in Ppseudo.

Lawler, E.L. and Lenstra, J.K. and Rinnooy Kan, A.H.G. and Shmoys, D.B. (1989). Sequencing and Scheduling: Algorithms and Complexity. None

Note: pseudo-polynomial for every fixed value.
-/
def p147_r0 (R : Reading F) : Prop :=
  PseudoPolyFixed (R.at p147) (lift (Ops.m p147))

/-- `1|prec;pj=1|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p148_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p148)

/-- `P|pj=1;bounded height|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p149_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p149)

/-- `P|pj=1;bounded height|Cmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p150_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p150)

/-- `P|Mj;prec;pj=1|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1978). Complexity of scheduling under precedence constraints. https://doi.org/10.1287/opre.26.1.22
-/
def p151_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p151)

/-- `1|chains;pj=1;rj|ΣwjCj`: ins strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1980). Complexity results for scheduling chains on a single machine. https://doi.org/10.1016/0377-2217(80)90111-3
-/
def p152_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p152)

/-- `1|chains;pj=1|ΣUj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1980). Complexity results for scheduling chains on a single machine. https://doi.org/10.1016/0377-2217(80)90111-3
-/
def p153_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p153)

/-- `P2|pj=1;intree|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1980). Complexity results for scheduling chains on a single machine. https://doi.org/10.1016/0377-2217(80)90111-3
-/
def p154_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p154)

/-- `P2|pj=1;outtree|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1980). Complexity results for scheduling chains on a single machine. https://doi.org/10.1016/0377-2217(80)90111-3
-/
def p155_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p155)

/-- `P2|Mj;intree;pj=1|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1980). Complexity results for scheduling chains on a single machine. https://doi.org/10.1016/0377-2217(80)90111-3
-/
def p156_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p156)

/-- `P2|Mj;outtree;pj=1|ΣwjCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. (1980). Complexity results for scheduling chains on a single machine. https://doi.org/10.1016/0377-2217(80)90111-3
-/
def p157_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p157)

/-- `1|rj|Lmax`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p158_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p158)

/-- `1|rj|Lmax`: is strongly NP-hard.

Elffers, Jan and de Weerdt, Mathijs (2014). Scheduling with two non-unit job lengths is NP-complete. https://arxiv.org/abs/1412.3095
-/
def p158_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p158)

/-- `1|rj|Lmax`, parameter pmax: is NP-hard.

Elffers, Jan and de Weerdt, Mathijs (2014). Scheduling with two non-unit job lengths is NP-complete. https://arxiv.org/abs/1412.3095
-/
def p158_r2 (R : Reading F) : Prop :=
  ParaNPHard (R.at p158) (lift (Ops.pmax p158))

/-- `1|rj|Lmax`, parameter #p: is NP-hard.

Elffers, Jan and de Weerdt, Mathijs (2014). Scheduling with two non-unit job lengths is NP-complete. https://arxiv.org/abs/1412.3095
-/
def p158_r3 (R : Reading F) : Prop :=
  ParaNPHard (R.at p158) (lift (Ops.numP p158))

/-- `1|rj|ΣCj`: is strongly NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p159_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p159)

/-- `1|rj|ΣCj`: randomized approximation ratio using alpha-points ≤1.5820.

Skutella, Martin (2006). List scheduling in order of $\alpha$-points on a single machine. https://doi.org/10.1007/11671541_9
-/
def p159_r1 (R : Reading F) : Prop :=
  RandomApprox (R.at p159) (const (1.5820 : ℝ))

/-- `P2||Cmax`: is NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p160_r0 (R : Reading F) : Prop :=
  NPHard (R.at p160)

/-- `P2|Mj|Cmax`: is NP-hard.

Lenstra, J.K. and Rinnooy Kan, A.H.G. and Brucker, P. (1977). Complexity of machine scheduling problems. https://doi.org/10.1016/s0167-5060(08)70743-x
-/
def p161_r0 (R : Reading F) : Prop :=
  NPHard (R.at p161)

/-- `1|prec;l;pj=1|Cmax`: is strongly NP-hard.

Leung, J.Y.-T. and Vornberger, O. and Witthoff, J.D. (1984). On some variants of the bandwidth minimization problem. https://doi.org/10.1137/0213040
-/
def p162_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p162)

/-- `1|prec;l;pj=1|Cmax`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p162_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p162)

/-- `1|chains;pj=1|ΣTj`: is strongly NP-hard.

Leung, J.Y.-T. and Young, G.H. (1990). Minimizing total tardiness on a single machine with precedence constraints. https://doi.org/10.1287/ijoc.2.4.346
-/
def p163_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p163)

/-- `1||ΣUj`: is in P.

Moore, J.M. (1968). An $n$ job, one machine sequencing algorithm for minimizing the number of late jobs. https://doi.org/10.1287/mnsc.15.1.102
-/
def p164_r0 (R : Reading F) : Prop :=
  InP (R.at p164)

/-- `1||ΣUj`: is in P.

Maxwell, W.L. (1970). On sequencing $n$ jobs on one machine to minimize the number of late jobs. https://doi.org/10.1287/mnsc.16.5.295
-/
def p164_r1 (R : Reading F) : Prop :=
  InP (R.at p164)

/-- `1||ΣUj`: is in P.

Sidney, J.B. (1973). An extension of Moore's due date algorithm. None
-/
def p164_r2 (R : Reading F) : Prop :=
  InP (R.at p164)

/-- `P|pj=1;intree|Lmax`: is in P.

Monma, C.L. (1982). Linear-time algorithms for scheduling on parallel processors. https://doi.org/10.1287/opre.30.1.116
-/
def p165_r0 (R : Reading F) : Prop :=
  InP (R.at p165)

/-- `1|chains;l;pj=p|Cmax`: is in P.

Munier, A. and Sourd, F. (2003). Scheduling chains on a single machine with non-negative time lags. https://doi.org/10.1007/s001860200242
-/
def p166_r0 (R : Reading F) : Prop :=
  InP (R.at p166)

/-- `1|chains;l=1;pj=p|ΣCj`: is in P.

Munier, A. and Sourd, F. (2003). Scheduling chains on a single machine with non-negative time lags. https://doi.org/10.1007/s001860200242
-/
def p167_r0 (R : Reading F) : Prop :=
  InP (R.at p167)

/-- `1|prec;pj=p;rj|Lmax`: is in P.

Simons, B. (1978). A fast algorithm for single processor scheduling. https://doi.org/10.1109/sfcs.1978.4
-/
def p168_r0 (R : Reading F) : Prop :=
  InP (R.at p168)

/-- `1|prec;pj=p;rj|ΣCj`: is in P.

Simons, B. (1983). Multiprocessor scheduling of unit-time jobs with arbitrary release times and deadlines. https://doi.org/10.1137/0212018
-/
def p169_r0 (R : Reading F) : Prop :=
  InP (R.at p169)

/-- `P|pj=p;rj|Lmax`: is in P.

Simons, B. (1983). Multiprocessor scheduling of unit-time jobs with arbitrary release times and deadlines. https://doi.org/10.1137/0212018
-/
def p170_r0 (R : Reading F) : Prop :=
  InP (R.at p170)

/-- `P|pj=p;rj|ΣCj`: is in P.

Simons, B. (1983). Multiprocessor scheduling of unit-time jobs with arbitrary release times and deadlines. https://doi.org/10.1137/0212018
-/
def p171_r0 (R : Reading F) : Prop :=
  InP (R.at p171)

/-- `P2|chains;pj=1|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p172_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p172)

/-- `P2|Mj;chains;pj=1|ΣwjCj`: is strongly NP-hard.

Timkovsky, V.G. (2003). Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity. https://doi.org/10.1016/s0377-2217(02)00767-1
-/
def p173_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p173)

/-- `1|chains;l=1;pj=1|ΣwjCj`: is strongly NP-hard.

Tanaev, V.S. and Sotskov, Y.N. and Strusevich, V.A. (1994). Scheduling theory. Multi-stage systems. https://doi.org/10.1007/978-94-011-1192-8
-/
def p174_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p174)

/-- `P|Mj;prec;pj=1|Cmax`: is strongly NP-hard.

Ullman, J.D. (1975). NP-complete scheduling problems. https://doi.org/10.1016/s0022-0000(75)80008-0
-/
def p175_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p175)

/-- `1|chains;l|Cmax`: is strongly NP-hard.

Wikum, E.D. and Llewellyn, D.C. and Nemhauser, G.L. (1994). One-machine generalized precedence constrained scheduling problems. https://doi.org/10.1016/0167-6377(94)90064-7
-/
def p176_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p176)

/-- `1|chains;lij;pj=1|Cmax`: is strongly NP-hard.

Yu, W. and Hoogeveen, H. and Lenstra, J.K. (2004). Minimizing makespan in a two-machine flow shop with delays and unit-time operations is NP-hard. https://doi.org/10.1023/b:josh.0000036858.59787.c2
-/
def p177_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p177)

/-- `1|chains;lij;pj=1|Cmax`: is strongly NP-hard.

Yu, W. (1996). The two-machine flow shop problem with delays and the one-machine total tardiness problem. None
-/
def p177_r1 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p177)

/-- `P2|outtree;pj=1;sizej|ΣCj`: is strongly NP-hard.

Zinder, Y. and Do, V.H. and Oguz, C. (2005). Computational complexity of some scheduling problems with multiprocessor tasks. https://doi.org/10.1016/j.disopt.2005.08.001
-/
def p178_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p178)

/-- `P2|intree;pj=1;sizej|ΣCj`: is strongly NP-hard.

Zinder, Y. and Do, V.H. (2005). Scheduling UET tasks on two parallel machines with the criteria of makespan and total completion time. None
-/
def p179_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p179)

/-- `1|pj=1;rj|ΣwjTj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p180_r0 (R : Reading F) : Prop :=
  InP (R.at p180)

/-- `1|pj=p|ΣwjTj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p181_r0 (R : Reading F) : Prop :=
  InP (R.at p181)

/-- `P|pj=p|ΣwjUj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p182_r0 (R : Reading F) : Prop :=
  InP (R.at p182)

/-- `P|pj=p|ΣwjTj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p183_r0 (R : Reading F) : Prop :=
  InP (R.at p183)

/-- `P;S1|sj=s;pj=p|ΣwjUj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p184_r0 (R : Reading F) : Prop :=
  InP (R.at p184)

/-- `P;S1|sj=1;pj=1;rj|ΣwjTj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p185_r0 (R : Reading F) : Prop :=
  InP (R.at p185)

/-- `P;S1|sj=s;pj=p|ΣwjTj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p186_r0 (R : Reading F) : Prop :=
  InP (R.at p186)

/-- `Q|pj=p;rj|Cmax`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p187_r0 (R : Reading F) : Prop :=
  InP (R.at p187)

/-- `Q|pj=p|ΣwjUj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p188_r0 (R : Reading F) : Prop :=
  InP (R.at p188)

/-- `Q|pj=p|ΣwjTj`: is in P.

unknown author (unknown year). see: Assignment Problem. None
-/
def p189_r0 (R : Reading F) : Prop :=
  InP (R.at p189)

/-- `P|pj=1;rj|ΣwjUj`: is in P.

unknown author (unknown year). see: Network Flow Problem. None
-/
def p190_r0 (R : Reading F) : Prop :=
  InP (R.at p190)

/-- `P|pj=1;rj|ΣwjTj`: is in P.

unknown author (unknown year). see: Network Flow Problem. None
-/
def p191_r0 (R : Reading F) : Prop :=
  InP (R.at p191)

/-- `P2|rj|ΣCj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p192_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p192)

/-- `P2|pj=1;chains;rj|ΣwjCj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p193_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p193)

/-- `P2|pj=1;chains|ΣUj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p194_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p194)

/-- `P2|pj=1;chains|ΣTj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p195_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p195)

/-- `P2|Mj;rj|ΣCj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p196_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p196)

/-- `P2|Mj;chains;pj=1;rj|ΣwjCj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p197_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p197)

/-- `P2|Mj;chains;pj=1|ΣUj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p198_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p198)

/-- `P2|Mj;chains;pj=1|ΣTj`: is strongly NP-hard.

unknown author (unknown year). see: Single Machine Problem. None
-/
def p199_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p199)

/-- `P|Mj|ΣwjZj`, parameter m: is strongly W[1]-hard.

Hermelin, Danny and Itzhaki, Yuval and Molter, Hendrik and Shabtay, Dvir (2024). On the Parameterized Complexity of Interval Scheduling with Eligible Machine Sets. https://doi.org/10.1016/j.jcss.2024.103533
-/
def p200_r0 (R : Reading F) : Prop :=
  StronglyWHard (R.at p200) 1 (lift (Ops.m p200))

/-- `P|Mj|ΣwjZj`, parameter m+pmax: is fixed parameter tractable.

Hermelin, Danny and Itzhaki, Yuval and Molter, Hendrik and Shabtay, Dvir (2024). On the Parameterized Complexity of Interval Scheduling with Eligible Machine Sets. https://doi.org/10.1016/j.jcss.2024.103533
-/
def p200_r1 (R : Reading F) : Prop :=
  IsFPT (R.at p200) (tplus (lift (Ops.m p200)) (lift (Ops.pmax p200)))

/-- `P|Mj|ΣwjZj`, parameter m: is in P.

Arkin, Esther M. and Silverberg, Ellen B. (1987). Scheduling Jobs with Fixed Start and End Times. https://doi.org/10.1016/0166-218X(87)90037-0

Note: in P for every fixed value.
-/
def p200_r2 (R : Reading F) : Prop :=
  InPFixed (R.at p200) (lift (Ops.m p200))

/-- `P|Mj|ΣZj`: is strongly NP-hard.

Arkin, Esther M. and Silverberg, Ellen B. (1987). Scheduling Jobs with Fixed Start and End Times. https://doi.org/10.1016/0166-218X(87)90037-0
-/
def p201_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p201)

/-- `P|Mj|ΣZj`, parameter pmax: is NP-hard.

Hermelin, Danny and Itzhaki, Yuval and Molter, Hendrik and Shabtay, Dvir (2024). On the Parameterized Complexity of Interval Scheduling with Eligible Machine Sets. https://doi.org/10.1016/j.jcss.2024.103533
-/
def p201_r1 (R : Reading F) : Prop :=
  ParaNPHard (R.at p201) (lift (Ops.pmax p201))

/-- `P||ΣwjZj`: is in P.

Arkin, Esther M. and Silverberg, Ellen B. (1987). Scheduling Jobs with Fixed Start and End Times. https://doi.org/10.1016/0166-218X(87)90037-0
-/
def p202_r0 (R : Reading F) : Prop :=
  InP (R.at p202)

/-- `P||ΣwjZj`: is in P.

Yannakakis, Mihalis and Gavril, Fănică (1987). The Maximum k-Colorable Subgraph Problem for Chordal Graphs. https://doi.org/10.1016/0020-0190(87)90107-4
-/
def p202_r1 (R : Reading F) : Prop :=
  InP (R.at p202)

/-- `P||ΣwjZj`: is in P.

Carlisle, Martin C. and Lloyd, Errol L. (1995). On the k-Coloring of Intervals. https://doi.org/10.1016/0166-218X(95)80003-M
-/
def p202_r2 (R : Reading F) : Prop :=
  InP (R.at p202)

/-- `P|Mj;pj=p|ΣZj`: is strongly NP-hard.

Marx, Dániel (2006). Precoloring Extension on Unit Interval Graphs. https://doi.org/10.1016/j.dam.2005.10.008
-/
def p203_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p203)

/-- `P|Mj;pj=p|ΣwjZj`: is strongly NP-hard.

Marx, Dániel (2006). Precoloring Extension on Unit Interval Graphs. https://doi.org/10.1016/j.dam.2005.10.008
-/
def p204_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p204)

/-- `1||ΣZj`: is in P.

Gavril, Fănică (1972). Algorithms for Minimum Coloring, Maximum Clique, Minimum Covering by Cliques, and Maximum Independent Set of a Chordal Graph. https://doi.org/10.1137/0201013
-/
def p205_r0 (R : Reading F) : Prop :=
  InP (R.at p205)

/-- `P||ΣZj`: is in P.

Yannakakis, Mihalis and Gavril, Fănică (1987). The Maximum k-Colorable Subgraph Problem for Chordal Graphs. https://doi.org/10.1016/0020-0190(87)90107-4
-/
def p206_r0 (R : Reading F) : Prop :=
  InP (R.at p206)

/-- `1||ΣwjZj`: is in P.

Carlisle, Martin C. and Lloyd, Errol L. (1995). On the k-Coloring of Intervals. https://doi.org/10.1016/0166-218X(95)80003-M
-/
def p207_r0 (R : Reading F) : Prop :=
  InP (R.at p207)

/-- `R||ΣwjZj`, parameter m: is in P.

Sung, Shao Chin and Vlach, Milan (2005). Maximizing Weighted Number of Just-in-Time Jobs on Unrelated Parallel Machines. https://doi.org/10.1007/s10951-005-2863-7

Note: in P for every fixed value.
-/
def p208_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p208) (lift (Ops.m p208))

/-- `1|2-dim partial order|ΣwjCj`: is in P.

Ambühl, Christoph and Mastrolilli, Monaldo (2009). Single machine precedence constrained scheduling is a vertex cover problem. https://doi.org/10.1007/s00453-008-9251-6
-/
def p209_r0 (R : Reading F) : Prop :=
  InP (R.at p209)

/-- `1|interval order|ΣwjCj`: is NP-hard.

Ambühl, Christoph and Mastrolilli, Monaldo and Mutsanas, Nikolaus and Svensson, Ola (2011). On the Approximability of Single-Machine Scheduling with Precedence Constraints. https://doi.org/10.1287/moor.1110.0512
-/
def p210_r0 (R : Reading F) : Prop :=
  NPHard (R.at p210)

/-- `P|opposing forest;pj=p|Cmax`, parameter m: is in P.

Garey, M.R. and Johnson, D.S. and Tarjan, R.E. and Yannakakis, M. (1983). Scheduling opposing forests. https://doi.org/10.1137/0604011

Note: in P for every fixed value.
-/
def p211_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p211) (lift (Ops.m p211))

/-- `P|opposing forest;pj=1|Cmax`: is NP-hard.

Garey, M.R. and Johnson, D.S. and Tarjan, R.E. and Yannakakis, M. (1983). Scheduling opposing forests. https://doi.org/10.1137/0604011
-/
def p212_r0 (R : Reading F) : Prop :=
  NPHard (R.at p212)

/-- `P|bounded height;pj=p|Cmax`, parameter m: is in P.

Dolev, Danny and Warmuth, Manfred K. (1984). Scheduling precedence graphs of bounded height. https://doi.org/10.1016/0196-6774(84)90039-7

Note: in P for every fixed value.
-/
def p213_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p213) (lift (Ops.m p213))

/-- `P|level order;pj=p|Cmax`, parameter m: is in P.

Dolev, Danny and Warmuth, Manfred K. (1985). Profile scheduling of opposing forests and level orders. https://doi.org/10.1137/0606066

Note: in P for every fixed value.
-/
def p214_r0 (R : Reading F) : Prop :=
  InPFixed (R.at p214) (lift (Ops.m p214))

/-- `P|interval order;pj=p|Cmax`: is in P.

Papadimitriou, Christos H. and Yannakakis, Mihalis (1979). Scheduling interval-ordered tasks. https://doi.org/10.1137/0208031
-/
def p215_r0 (R : Reading F) : Prop :=
  InP (R.at p215)

/-- `P|interval order;pj=p|ΣCj`: is in P.

Möhring, Rolf H. (1989). Computationally Tractable Classes of Ordered Sets. https://doi.org/10.1007/978-94-009-2639-4_4
-/
def p216_r0 (R : Reading F) : Prop :=
  InP (R.at p216)

/-- `P|quasi-interval order;pj=p|Cmax`: is in P.

Moukrim, Aziz (1999). Optimal scheduling on parallel machines for a new order class. https://doi.org/10.1016/s0167-6377(99)00003-6
-/
def p217_r0 (R : Reading F) : Prop :=
  InP (R.at p217)

/-- `P|over-interval order;pj=p|Cmax`: is in P.

Chardon, Marc and Moukrim, Aziz (2005). The Coffman--Graham Algorithm Optimally Solves UET Task Systems with Overinterval Orders. https://doi.org/10.1137/s0895480101394999
-/
def p218_r0 (R : Reading F) : Prop :=
  InP (R.at p218)

/-- `P|DC-graph;pj=p|Cmax`: is in P.

Kubiak, Wieslaw and Rebaine, Djamal and Potts, Chris (2009). Optimality of HLF for scheduling divide-and-conquer UET task graphs on identical parallel processors. https://doi.org/10.1016/j.disopt.2008.09.001
-/
def p219_r0 (R : Reading F) : Prop :=
  InP (R.at p219)

/-- `P|prec;l=1;pj=1|Cmax`: polynomial time approximation ratio is ≥5/4.

Hoogeveen, JA and Lenstra, Jan Karel and Veltman, Bart (1994). Three, four, five, six, or the complexity of scheduling with communication delays. https://doi.org/10.1016/0167-6377(94)90024-8

Note: read as holding unless P = NP.
-/
def p220_r0 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p220) ((5 : ℝ) / 4)

/-- `R|rj|ΣCj`: is APX-hard.

Hoogeveen, Han and Schuurman, Petra and Woeginger, Gerhard J (2001). Non-approximability results for scheduling problems with minsum criteria. https://doi.org/10.1287/ijoc.13.2.157.10520

Note: stated as the consequence: no PTAS unless P = NP.
-/
def p221_r0 (R : Reading F) : Prop :=
  NoPTAS (R.at p221)

/-- `R||ΣwjCj`: is APX-hard.

Hoogeveen, Han and Schuurman, Petra and Woeginger, Gerhard J (2001). Non-approximability results for scheduling problems with minsum criteria. https://doi.org/10.1287/ijoc.13.2.157.10520

Note: stated as the consequence: no PTAS unless P = NP.
-/
def p222_r0 (R : Reading F) : Prop :=
  NoPTAS (R.at p222)

/-- `R||ΣwjCj`: has a polynomial-time 1.488-approximation.

Sungjin Im and Maryam Shadloo (2020). Weighted Completion Time Minimization for Unrelated Machines via Iterative Fair Contention Resolution. https://doi.org/10.1137/1.9781611975994.170
-/
def p222_r1 (R : Reading F) : Prop :=
  Approx (R.at p222) (const (1.488 : ℝ))

/-- `R||ΣwjCj`, parameter pmax+wmax+#kind: is fixed parameter tractable.

Knop, Dušan and Koutecký, Martin (2017). Scheduling meets n-fold integer programming. https://doi.org/10.48550/arXiv.1603.02611
-/
def p222_r2 (R : Reading F) : Prop :=
  IsFPT (R.at p222) (tplus (tplus (lift (Ops.pmax p222)) (lift (Ops.wmax p222))) (lift (Ops.kinds p222)))

/-- `P|prec;pj=1|ΣCj`: is  APX-hard.

Hoogeveen, Han and Schuurman, Petra and Woeginger, Gerhard J (2001). Non-approximability results for scheduling problems with minsum criteria. https://doi.org/10.1287/ijoc.13.2.157.10520

Note: stated as the consequence: no PTAS unless P = NP.
-/
def p223_r0 (R : Reading F) : Prop :=
  NoPTAS (R.at p223)

/-- `P|prec;l=1;pj=1|ΣCj`: is APX-hard.

Hoogeveen, Han and Schuurman, Petra and Woeginger, Gerhard J (2001). Non-approximability results for scheduling problems with minsum criteria. https://doi.org/10.1287/ijoc.13.2.157.10520

Note: stated as the consequence: no PTAS unless P = NP.
-/
def p224_r0 (R : Reading F) : Prop :=
  NoPTAS (R.at p224)

/-- `P|rj|ΣwjCj`: has a PTAS.

Afrati, Foto and Bampis, Evripidis and Chekuri, Chandra and Karger, David and Kenyon, Claire and Khanna, Sanjeev and Milis, Ioannis and Queyranne, Maurice and Skutella, Martin and Stein, Clifford and others (1999). Approximation schemes for minimizing average weighted completion time with release dates. https://doi.org/10.1109/sffcs.1999.814574
-/
def p225_r0 (R : Reading F) : Prop :=
  PTAS (R.at p225)

/-- `P|rj|ΣwjCj`: randomized approximation ratio ≤2.

Schulz, Andreas S and Skutella, Martin (1997). Scheduling-LPs bear probabilities randomized approximations for min-sum criteria. https://doi.org/10.1007/3-540-63397-9_32
-/
def p225_r1 (R : Reading F) : Prop :=
  RandomApprox (R.at p225) (const (2 : ℝ))

/-- `1|online-rj|ΣwjCj`: deterministic competitive ratio ≤2.

Han Hoogeveen and Arjen P. A. Vestjens (1996). Optimal On-Line Algorithms for Single-Machine Scheduling. https://doi.org/10.1007/3-540-61310-2_30
-/
def p226_r0 (R : Reading F) : Prop :=
  DetCompetitive (R.at p226) (const (2 : ℝ))

/-- `1|online-rj|ΣwjCj`: deterministic competitive ratio ≥2.

Han Hoogeveen and Arjen P. A. Vestjens (1996). Optimal On-Line Algorithms for Single-Machine Scheduling. https://doi.org/10.1007/3-540-61310-2_30
-/
def p226_r1 (R : Reading F) : Prop :=
  DetLowerBound (R.at p226) (2 : ℝ)

/-- `1|dj=d|ΣwjTj`: has an FPTAS.

Kellerer, H. and Strusevich, V.A. (2006). A fully polynomial approximation scheme for the single machine weighted total tardiness problem with a common due date. https://doi.org/10.1016/j.tcs.2006.08.030
-/
def p227_r0 (R : Reading F) : Prop :=
  FPTAS (R.at p227)

/-- `1|dj=d|ΣwjTj`: is NP-hard.

JUAN Jinjiang (1992). The NP-hardness of the single machine common due date weighted tardiness problem. None
-/
def p227_r1 (R : Reading F) : Prop :=
  NPHard (R.at p227)

/-- `1|dj=d|ΣwjTj`: is in Ppseudo with time complexity O(n^2d).

Lawler, E.L. and Moore, J.M. (1969). A functional equation and its application to resource allocation and sequencing problems. https://doi.org/10.1287/mnsc.16.1.77

Note: d is the (common) due date.
-/
def p227_r2 (R : Reading F) : Prop :=
  DecidesWithin (R.at p227) (fun x => (Ops.n p227 x) ^ 2 * (Finset.univ.sup (Ops.due p227 x)))

/-- `1|pj=1;prec;lij≤0|Lmax`: is NP-hard by reduction from 3-SAT.

Manaa, A. and Hanen, C. (2010). On scheduling with negative time lags. None
-/
def p228_r0 (R : Reading F) : Prop :=
  NPHard (R.at p228)

/-- `P|rj;pj=1;sizej∈1,m|Lmax`: the decision version is solvable in O(n^3).

Christoph Dürr and Mathilde Hurand (2006). Finding total unimodularity in optimization problems solved by linear programs. https://doi.org/10.1007/11841036_30
-/
def p229_r0 (R : Reading F) : Prop :=
  DecidesWithin (R.at p229) (fun x => (Ops.n p229 x) ^ 3)

/-- `P|rj;pj=1;sizej∈1,m|Lmax`: can be decided with an LP of O(n^2) var.

Baptiste, P. and Schieber, B. (2003). A note on scheduling tall/small multiprocessor tasks with unit processing time to minimize maximum tardiness. https://doi.org/10.1023/a:1024012811536

Note: the size of the linear program is not stated; solving it gives polynomial time.
-/
def p229_r1 (R : Reading F) : Prop :=
  InP (R.at p229)

/-- `1|rj;pj=p|ΣUj`: is solvable in O(n^5).

Marek Chrobak and Christoph Dürr and Wojciech Jawor and Lukasz Kowalik and Maciej Kurowski (2006). A Note on Scheduling Equal-Length Jobs to Maximize Throughput. https://doi.org/10.1007/s10951-006-5595-4
-/
def p230_r0 (R : Reading F) : Prop :=
  DecidesWithin (R.at p230) (fun x => (Ops.n p230 x) ^ 5)

/-- `P2|rj;pj=1;sizej|Lmax`: is in P.

Baptiste, P. and Schieber, B. (2003). A note on scheduling tall/small multiprocessor tasks with unit processing time to minimize maximum tardiness. https://doi.org/10.1023/a:1024012811536
-/
def p231_r0 (R : Reading F) : Prop :=
  InP (R.at p231)

/-- `P2|rj|Lmax`, parameter pw(I): is para-NP-complete.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4
-/
def p232_r0 (R : Reading F) : Prop :=
  ParaNPHard (R.at p232) (Ops.pw p232)

/-- `P|Mj;prec;rj|Lmax`, parameter pw(I): does not admit a fixed parameter algorithm unless FPT=para-NP.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4

Note: stated as para-NP-hardness, which the claim rests on.
-/
def p233_r0 (R : Reading F) : Prop :=
  ParaNPHard (R.at p233) (Ops.pw p233)

/-- `P|Mj;prec;rj|Lmax`, parameter pmax: does not admit a fixed parameter algorithm unless FPT=para-NP.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4

Note: stated as para-NP-hardness, which the claim rests on.
-/
def p233_r1 (R : Reading F) : Prop :=
  ParaNPHard (R.at p233) (lift (Ops.pmax p233))

/-- `P|Mj;prec;rj|Lmax`, parameter slackmax: does not admit a fixed parameter algorithm unless FPT=para-NP.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4

Note: stated as para-NP-hardness, which the claim rests on.
-/
def p233_r2 (R : Reading F) : Prop :=
  ParaNPHard (R.at p233) (Ops.slackmax p233)

/-- `P|Mj;prec;rj;l|Cmax`, parameter pw(I)+pmax: is fixed parameter tractable.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4
-/
def p234_r0 (R : Reading F) : Prop :=
  IsFPT (R.at p234) (tplus (Ops.pw p234) (lift (Ops.pmax p234)))

/-- `P|Mj;prec;rj;l|Cmax`, parameter pw(I)+slackmax: is fixed parameter tractable.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4
-/
def p234_r1 (R : Reading F) : Prop :=
  IsFPT (R.at p234) (tplus (Ops.pw p234) (Ops.slackmax p234))

/-- `P|Mj;prec;rj;l|Lmax`, parameter pw(I)+pmax: is fixed parameter tractable.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4
-/
def p235_r0 (R : Reading F) : Prop :=
  IsFPT (R.at p235) (tplus (Ops.pw p235) (lift (Ops.pmax p235)))

/-- `P|Mj;prec;rj;l|Lmax`, parameter pw(I)+slackmax: is fixed parameter tractable.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4
-/
def p235_r1 (R : Reading F) : Prop :=
  IsFPT (R.at p235) (tplus (Ops.pw p235) (Ops.slackmax p235))

/-- `P|Mj;prec;rj;d̄j=d̄|Cmax`, parameter pw(I)+pmax: is fixed parameter tractable.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4
-/
def p236_r0 (R : Reading F) : Prop :=
  IsFPT (R.at p236) (tplus (Ops.pw p236) (lift (Ops.pmax p236)))

/-- `P|Mj;prec;rj;d̄j=d̄|Cmax`, parameter pw(I)+slackmax: is fixed parameter tractable.

Hanen, Claire and Munier Kordon, Alix (2024). Fixed-parameter tractability of scheduling dependent typed tasks subject to release times and deadlines. https://doi.org/10.1007/s10951-023-00788-4
-/
def p236_r1 (R : Reading F) : Prop :=
  IsFPT (R.at p236) (tplus (Ops.pw p236) (Ops.slackmax p236))

/-- `1|rj|ΣwjUj`, parameter #d+#r: is W[1]-hard even if #w=1.

Matthias Kaul and Matthias Mnich and Hendrik Molter (2024). Single-Machine Scheduling to Minimize the Number of Tardy Jobs with Release Dates. https://doi.org/10.48550/arXiv.2408.12967

Note: stated strongly: the source proves strong W[1]-hardness (Theorem 2); with binary numbers the problem is NP-hard already for a constant number of release and due dates; the restriction to one weight is not stated.
-/
def p237_r0 (R : Reading F) : Prop :=
  StronglyWHard (R.at p237) 1 (tplus (lift (Ops.numD p237)) (lift (Ops.numR p237)))

/-- `1|rj|ΣwjUj`, parameter #p+#d+#r: is fixed parameter tractable.

Matthias Kaul and Matthias Mnich and Hendrik Molter (2024). Single-Machine Scheduling to Minimize the Number of Tardy Jobs with Release Dates. https://doi.org/10.48550/arXiv.2408.12967
-/
def p237_r1 (R : Reading F) : Prop :=
  IsFPT (R.at p237) (tplus (tplus (lift (Ops.numP p237)) (lift (Ops.numD p237))) (lift (Ops.numR p237)))

/-- `1|rj|ΣwjUj`, parameter #p+#w+#d: is fixed parameter tractable.

Matthias Kaul and Matthias Mnich and Hendrik Molter (2024). Single-Machine Scheduling to Minimize the Number of Tardy Jobs with Release Dates. https://doi.org/10.48550/arXiv.2408.12967
-/
def p237_r2 (R : Reading F) : Prop :=
  IsFPT (R.at p237) (tplus (tplus (lift (Ops.numP p237)) (lift (Ops.numW p237))) (lift (Ops.numD p237)))

/-- `1|rj|ΣwjUj`, parameter #p+#w+#r: is fixed parameter tractable.

Matthias Kaul and Matthias Mnich and Hendrik Molter (2024). Single-Machine Scheduling to Minimize the Number of Tardy Jobs with Release Dates. https://doi.org/10.48550/arXiv.2408.12967
-/
def p237_r3 (R : Reading F) : Prop :=
  IsFPT (R.at p237) (tplus (tplus (lift (Ops.numP p237)) (lift (Ops.numW p237))) (lift (Ops.numR p237)))

/-- `1|rj|ΣwjUj`, parameter #d+#r: is strongly W[1]-hard.

Kaul, Matthias and Mnich, Matthias and Molter, Hendrik (2024). Single-machine scheduling to minimize the number of tardy jobs with release dates. https://arxiv.org/pdf/2408.12967
-/
def p237_r4 (R : Reading F) : Prop :=
  StronglyWHard (R.at p237) 1 (tplus (lift (Ops.numD p237)) (lift (Ops.numR p237)))

/-- `1|rj|ΣwjUj`, parameter #p+#d+#r: is fixed parameter tractable.

Kaul, Matthias and Mnich, Matthias and Molter, Hendrik (2024). Single-machine scheduling to minimize the number of tardy jobs with release dates. https://arxiv.org/pdf/2408.12967
-/
def p237_r5 (R : Reading F) : Prop :=
  IsFPT (R.at p237) (tplus (tplus (lift (Ops.numP p237)) (lift (Ops.numD p237))) (lift (Ops.numR p237)))

/-- `1|rj|ΣwjUj`, parameter #p+#d+#w: is fixed parameter tractable.

Kaul, Matthias and Mnich, Matthias and Molter, Hendrik (2024). Single-machine scheduling to minimize the number of tardy jobs with release dates. https://arxiv.org/pdf/2408.12967
-/
def p237_r6 (R : Reading F) : Prop :=
  IsFPT (R.at p237) (tplus (tplus (lift (Ops.numP p237)) (lift (Ops.numD p237))) (lift (Ops.numW p237)))

/-- `1|rj|ΣwjUj`, parameter #p+#w+#r: is fixed parameter tractable.

Kaul, Matthias and Mnich, Matthias and Molter, Hendrik (2024). Single-machine scheduling to minimize the number of tardy jobs with release dates. https://arxiv.org/pdf/2408.12967
-/
def p237_r7 (R : Reading F) : Prop :=
  IsFPT (R.at p237) (tplus (tplus (lift (Ops.numP p237)) (lift (Ops.numW p237))) (lift (Ops.numR p237)))

/-- `P|rj;pj=p|ΣUj`: is NP-hard.

Heeger,Klaus and Molter,Hendrik (2024). Minimizing the Number of Tardy Jobs with Uniform Processing Times on Parallel Machines. https://arxiv.org/abs/2404.14208
-/
def p238_r0 (R : Reading F) : Prop :=
  NPHard (R.at p238)

/-- `P|rj;pj=p|ΣUj`, parameter m: is W[2]-hard.

Heeger,Klaus and Molter,Hendrik (2024). Minimizing the Number of Tardy Jobs with Uniform Processing Times on Parallel Machines. https://arxiv.org/abs/2404.14208

Note: stated strongly: every number of the source's reduction is polynomial in the input (Theorem 3).
-/
def p238_r1 (R : Reading F) : Prop :=
  StronglyWHard (R.at p238) 2 (lift (Ops.m p238))

/-- `P|rj;prec|ΣwjCj`: has a polynomial-time 4-approximation.

Queyranne, Maurice and Schulz, Andreas S. (2006). Approximation Bounds for a General Class of Precedence Constrained Parallel Machine Scheduling Problems. https://doi.org/10.1137/S0097539799358094
-/
def p239_r0 (R : Reading F) : Prop :=
  Approx (R.at p239) (const (4 : ℝ))

/-- `P|rj;prec|ΣwjCj`: has a polynomial-time (2+2ln 2+epsilon)-approximation.

Sven Jäger (2018). Approximating total weighted completion time on identical parallel machines with precedence constraints and release dates. https://doi.org/10.1016/j.orl.2018.07.006
-/
def p239_r1 (R : Reading F) : Prop :=
  ∀ ε : ℚ, 0 < ε → Approx (R.at p239) (const (2 + 2 * Real.log 2 + ε))

/-- `P|prec|ΣwjCj`: has a polynomial-time (2+2ln 2+epsilon)-approximation.

Li, Shi (2020). Scheduling to Minimize Total Weighted Completion Time via Time-Indexed Linear Programming Relaxations. https://doi.org/10.1137/17M1156332
-/
def p240_r0 (R : Reading F) : Prop :=
  ∀ ε : ℚ, 0 < ε → Approx (R.at p240) (const (2 + 2 * Real.log 2 + ε))

/-- `P|prec;pj=1|ΣwjCj`: has a polynomial-time (1+sqrt 2)-approximation.

Li, Shi (2020). Scheduling to Minimize Total Weighted Completion Time via Time-Indexed Linear Programming Relaxations. https://doi.org/10.1137/17M1156332
-/
def p241_r0 (R : Reading F) : Prop :=
  Approx (R.at p241) (const (1 + Real.sqrt 2))

/-- `P|prec;pj=1|ΣwjCj`, parameter m: has a polynomial-time (2+epsilon)-approximation.

Shashwat Garg and Janardhan Kulkarni and Shi Li (2019). Lift and Project Algorithms for Precedence Constrained Scheduling to Minimize Completion Time. https://doi.org/10.1137/1.9781611975482.95

Note: for every fixed value.
-/
def p241_r1 (R : Reading F) : Prop :=
  ∀ ε : ℚ, 0 < ε → ApproxFixed (R.at p241) (Ops.m p241) (const (2 + ε))

/-- `Q|prec|ΣwjCj`: has a polynomial-time O(log m/loglog m)-approximation.

Li, Shi (2020). Scheduling to Minimize Total Weighted Completion Time via Time-Indexed Linear Programming Relaxations. https://doi.org/10.1137/17M1156332

Note: m + 3 inside the logarithms keeps the bound positive for small m.
-/
def p242_r0 (R : Reading F) : Prop :=
  ∃ C : ℝ, Approx (R.at p242) (fun x => C * (Real.log (((Ops.m p242 x) : ℝ) + 3) / Real.log (Real.log (((Ops.m p242 x) : ℝ) + 3))))

/-- `1|pj=p;online-rj|ΣUj`: algorithm RandLock has randomized competitive ratio 5/3.

Chrobak, Marek and Jawor, Wojciech and Sgall, Jiří and Tichỳ, Tomáš (2007). Online scheduling of equal-length jobs: Randomization and restarts help. https://doi.org/10.1137/s0097539704446608

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p243_r0 (R : Reading F) : Prop :=
  RandCompetitiveKept (R.at p243) (Ops.totalW p243) (const ((5 : ℝ) / 3))

/-- `1|pj=p;online-rj|ΣUj`: Greedy algorithm has deterministc competitive ratio exactly 2.

BARUAH, S (1994). On-line scheduling to maximize task completions. https://doi.org/10.1109/real.1994.342713

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p243_r1 (R : Reading F) : Prop :=
  DetCompetitiveKept (R.at p243) (Ops.totalW p243) (const (2 : ℝ)) ∧ DetLowerBoundKept (R.at p243) (Ops.totalW p243) (2 : ℝ)

/-- `1|pj=p;online-rj|ΣUj`: every deterministic algorithm has deterministc competitive ratio ≥2.

BARUAH, S (1994). On-line scheduling to maximize task completions. https://doi.org/10.1109/real.1994.342713

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p243_r2 (R : Reading F) : Prop :=
  DetLowerBoundKept (R.at p243) (Ops.totalW p243) (2 : ℝ)

/-- `1|pj=p;online-rj|ΣUj`: randomized competitive ratio is ≥4/3.

Sally A Goldman and Jyoti Parwatikar and Subhash Suri (2000). Online Scheduling with Hard Deadlines. https://www.sciencedirect.com/science/article/pii/S019667749991060X

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p243_r3 (R : Reading F) : Prop :=
  RandLowerBoundKept (R.at p243) (Ops.totalW p243) ((4 : ℝ) / 3)

/-- `1|pj=p;online-rj|ΣUj`: algorithm Procrastinator has randomized competitive ratio 5/3.

Shahkooh, Neda Abbasi  and Böhm, Martin  and Jeż, Łukasz (2022). Barely Random Algorithms for Online Scheduling with Equal Job Sizes. None

Note: measured on the kept weight (total weight minus the cost), as the source maximizes it.
-/
def p243_r4 (R : Reading F) : Prop :=
  RandCompetitiveKept (R.at p243) (Ops.totalW p243) (const ((5 : ℝ) / 3))

/-- `P∞|pj=1;prec;c=1|Cmax`: cannot be approximated below ratio 7/6 unless P=NP.

Hoogeveen, JA and Lenstra, Jan Karel and Veltman, Bart (1994). Three, four, five, six, or the complexity of scheduling with communication delays. https://doi.org/10.1016/0167-6377(94)90024-8
-/
def p244_r0 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p244) ((7 : ℝ) / 6)

/-- `P|pj=1;prec;c=1|Cmax`: cannot be approximated below ratio 5/4 unless P=NP.

Hoogeveen, JA and Lenstra, Jan Karel and Veltman, Bart (1994). Three, four, five, six, or the complexity of scheduling with communication delays. https://doi.org/10.1016/0167-6377(94)90024-8
-/
def p245_r0 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p245) ((5 : ℝ) / 4)

/-- `P|pj=1;prec;c=1|Cmax`: has a polynomial time 4/3-approximation.

Munier, Alix and König, Jean-Claude (1997). A Heuristic for a Scheduling Problem with Communication Delays. http://pubsonline.informs.org/doi/10.1287/opre.45.1.145
-/
def p245_r1 (R : Reading F) : Prop :=
  Approx (R.at p245) (const ((4 : ℝ) / 3))

/-- `P|pj=1;prec;c=1|Cmax`, parameter m: can be approximated within ratio 3-2/m.

Rayward-Smith, Victor J (1987). UET scheduling with unit interprocessor communication delays. https://doi.org/10.1016/0166-218x(87)90042-4
-/
def p245_r2 (R : Reading F) : Prop :=
  Approx (R.at p245) (fun x => 3 - 2 / ((Ops.m p245 x) : ℝ))

/-- `P∞|pj=1;prec;c|Cmax`: cannot be approximated below ratio (1+1/(c+4)) unless P=NP.

Giroudeau, Rodolphe and Konig, Jean-Claude and Moulai, Farida Kamila and Palaysi, Jérôme (2008). Complexity and approximation for precedence constrained scheduling problems with large communication delays. https://doi.org/10.1016/j.tcs.2008.03.027

Note: for every value c of the communication delay.
-/
def p246_r0 (R : Reading F) : Prop :=
  ∀ c : ℕ, NoApproxBelowOn (R.at p246) {x | (Ops.cmax p246 x) = c} (1 + 1 / ((c : ℝ) + 4))

/-- `P|pj=1;prec;c|Cmax`: cannot be approximated below ratio 5/4 unless P=NP.

Bampis, Evripidis and Giannakos, Aristotelis and König, Jean-Claude (1996). On the complexity of scheduling with large communication delays. https://doi.org/10.1016/0377-2217(96)00124-5
-/
def p247_r0 (R : Reading F) : Prop :=
  NoApproxBelow (R.at p247) ((5 : ℝ) / 4)

/-- `P|prec;c|Cmax`: has a randomized, expected polynomial time O(log c· log m)-approximation.

Davies, Sami and Kulkarni, Janardhan and Rothvoss, Thomas and Tarnawski, Jakub and Zhang, Yihao (2020). Scheduling with Communication Delays via LP Hierarchies and Clustering. https://ieeexplore.ieee.org/document/9317899/

Note: c is the largest communication delay; + 2 inside the logarithms keeps the bound positive.
-/
def p248_r0 (R : Reading F) : Prop :=
  ∃ C : ℝ, RandomApproxExpected (R.at p248) (fun x => C * (Real.log (((Ops.cmax p248 x) : ℝ) + 2) * Real.log (((Ops.m p248 x) : ℝ) + 2)))

/-- `P∞|prec;c|Cmax`: has a randomized, expected polynomial time O(log c· log n)-approximation.

Davies, Sami and Kulkarni, Janardhan and Rothvoss, Thomas and Tarnawski, Jakub and Zhang, Yihao (2020). Scheduling with Communication Delays via LP Hierarchies and Clustering. https://ieeexplore.ieee.org/document/9317899/

Note: c is the largest communication delay; + 2 inside the logarithms keeps the bound positive.
-/
def p249_r0 (R : Reading F) : Prop :=
  ∃ C : ℝ, RandomApproxExpected (R.at p249) (fun x => C * (Real.log (((Ops.cmax p249 x) : ℝ) + 2) * Real.log (((Ops.n p249 x) : ℝ) + 2)))

/-- `Q|prec;c|ΣwjCj`: has a randomized expected polynomial time O(M^2 log^2 n)-approxation, where M = log(smax/smin) is the logarithm of the ratios between the fastest and slowest machine.

Davies, Sami and Kulkarni, Janardhan and Rothvoss, Thomas and Tarnawski, Jakub and Zhang, Yihao (2021). Scheduling with Communication Delays via LP Hierarchies and Clustering II: Weighted Completion Times on Related Machines. https://doi.org/10.1137/1.9781611976465.176

Note: M + 1 and n + 2 keep the bound positive.
-/
def p250_r0 (R : Reading F) : Prop :=
  ∃ C : ℝ, RandomApproxExpected (R.at p250) (fun x => C * ((Real.log (Ops.speedRatio p250 x) + 1) ^ 2 * Real.log (((Ops.n p250 x) : ℝ) + 2) ^ 2))

/-- `Q|prec;c|ΣwjCj`: has a polynomial time O(log^2 n log^2 m log c/loglog c)-approximation.

Maiti, Biswaroop and Rajaraman, Rajmohan and Stalfa, David and Svitkina, Zoya and Vijayaraghavan, Aravindan (2020). Scheduling Precedence-Constrained Jobs on Related Machines with Communication Delay. https://ieeexplore.ieee.org/document/9317889/

Note: c is the largest communication delay; the shifts inside the logarithms keep the bound positive.
-/
def p250_r1 (R : Reading F) : Prop :=
  ∃ C : ℝ, Approx (R.at p250) (fun x => C * (Real.log (((Ops.n p250 x) : ℝ) + 2) ^ 2 * Real.log (((Ops.m p250 x) : ℝ) + 2) ^ 2 * Real.log (((Ops.cmax p250 x) : ℝ) + 3) / Real.log (Real.log (((Ops.cmax p250 x) : ℝ) + 3))))

/-- `Q|prec;c;pj=1|ΣwjCj`: has a randomized expected polynomial time O(M log^2 n)-approxation, where M = log(smax/smin) is the logarithm of the ratios between the fastest and slowest machine.

Davies, Sami and Kulkarni, Janardhan and Rothvoss, Thomas and Tarnawski, Jakub and Zhang, Yihao (2021). Scheduling with Communication Delays via LP Hierarchies and Clustering II: Weighted Completion Times on Related Machines. https://doi.org/10.1137/1.9781611976465.176

Note: M + 1 and n + 2 keep the bound positive.
-/
def p251_r0 (R : Reading F) : Prop :=
  ∃ C : ℝ, RandomApproxExpected (R.at p251) (fun x => C * ((Real.log (Ops.speedRatio p251 x) + 1) * Real.log (((Ops.n p251 x) : ℝ) + 2) ^ 2))

/-- `1|rj|ΣUj`: is strongly NP-hard.

Elffers, Jan and de Weerdt, Mathijs (2014). Scheduling with two non-unit job lengths is NP-complete. https://arxiv.org/abs/1412.3095
-/
def p252_r0 (R : Reading F) : Prop :=
  StronglyNPHard (R.at p252)

/-- `1|rj|ΣUj`, parameter pmax: is NP-hard.

Elffers, Jan and de Weerdt, Mathijs (2014). Scheduling with two non-unit job lengths is NP-complete. https://arxiv.org/abs/1412.3095
-/
def p252_r1 (R : Reading F) : Prop :=
  ParaNPHard (R.at p252) (lift (Ops.pmax p252))

/-- `P|HM|Cmax`, parameter #p: is fixed parameter tractable.

Koana, Tomohiro and Kumabe, Soh (2026). High-Multiplicity Bin Packing is FPT. https://arxiv.org/abs/2609.16923
-/
def p254_r0 (R : Reading F) : Prop :=
  IsFPT (R.at p254) (lift (Ops.numP p254))

end Lax434175.ZooParallelResults
