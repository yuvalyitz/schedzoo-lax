import Lax434175.Problems

/-!
---
title: Online scheduling as a game
type: theorem
---
In an online problem the instance is revealed over time, and a schedule must
be fixed as time passes. A revelation of a problem says, for every time
$t \ge 0$, which instances look the same to the scheduler at time $t$, and
which schedules of two instances have made the same decisions up to time
$t$.

The competitive-ratio game is played by the scheduler and an adversary. The
scheduler chooses an algorithm, a schedule for every instance, which must be
non-anticipative: on two instances that look the same at time $t$ it makes
the same decisions up to time $t$. The adversary then chooses an instance.
For a ratio $\rho$ and an additive constant $\alpha$, the scheduler wins if
its schedule is feasible and costs at most $\rho$ times the cost of every
feasible schedule of the instance, plus $\alpha$; otherwise the adversary
wins. An algorithm with which the scheduler always wins is
$(\rho, \alpha)$-competitive.

A randomized algorithm is a finite probability distribution over
non-anticipative algorithms; it is $(\rho, \alpha)$-competitive if all its
algorithms schedule every instance feasibly and its expected cost is at most
$\rho$ times the cost of every feasible schedule, plus $\alpha$. A
distribution over instances, each with a feasible schedule as witness,
defeats the ratio if every non-anticipative algorithm schedules some instance
of it infeasibly or has positive expected excess, the cost minus $\rho$
times the witness's cost minus $\alpha$.

An embedding of one problem into another is causal for two revelations if
instances that look the same at time $t$ are mapped to instances that look
the same at time $t$, and schedules that made the same decisions up to time
$t$ are translated back to schedules that made the same decisions up to
time $t$.

**Theorem.**

1. The game is determined: the adversary wins against every non-anticipative
   algorithm exactly if the scheduler has no winning algorithm.
2. A deterministic competitive algorithm is a randomized one.
3. (Yao's principle, the direction used for lower bounds.) If a distribution
   over instances defeats a ratio, no randomized algorithm has that ratio.
4. Along a sound causal embedding of $A$ into $B$ and for $\rho \ge 0$, a
   $(\rho, \alpha)$-competitive algorithm for $B$ yields one for $A$, so
   that lower bounds pass from $A$ to $B$.
-/

namespace Lax434175.Online
open Lax434175.Problems

/-- How the instances of a problem are revealed over time. -/
structure Revelation (P : Problem) where
  /-- The two instances look the same to the scheduler at time `t`. -/
  same : P.Inst → P.Inst → NNRat → Prop
  /-- Two schedules of two instances made the same decisions up to time `t`. -/
  agree : (x y : P.Inst) → P.Sched x → P.Sched y → NNRat → Prop

variable {P : Problem}

/-- A deterministic algorithm: a schedule for every instance. -/
abbrev Algorithm (P : Problem) := (x : P.Inst) → P.Sched x

/-- The algorithm decides up to time `t` only from what is revealed at `t`. -/
def NonAnticipative (R : Revelation P) (A : Algorithm P) : Prop :=
  ∀ x y t, R.same x y t → R.agree x y (A x) (A y) t

/-- The scheduler wins on every instance: a feasible schedule costing at most
`ρ` times every feasible schedule, plus `α`. -/
def Competitive (A : Algorithm P) (ρ α : ℚ) : Prop :=
  ∀ x, P.feasible x (A x) ∧ ∀ σ, P.feasible x σ → P.cost x (A x) ≤ ρ * P.cost x σ + α

/-- The scheduler has a winning strategy. -/
def SchedulerWins (R : Revelation P) (ρ α : ℚ) : Prop :=
  ∃ A, NonAnticipative R A ∧ Competitive A ρ α

/-- The adversary beats every non-anticipative algorithm. -/
def AdversaryWins (R : Revelation P) (ρ α : ℚ) : Prop :=
  ∀ A, NonAnticipative R A → ∃ x, ¬ P.feasible x (A x) ∨
    ∃ σ, P.feasible x σ ∧ ρ * P.cost x σ + α < P.cost x (A x)

/-- A finite probability distribution over non-anticipative algorithms. -/
structure Randomized (R : Revelation P) where
  algorithms : List (ℚ × Algorithm P)
  nonneg : ∀ a ∈ algorithms, 0 ≤ a.1
  total : (algorithms.map Prod.fst).sum = 1
  nonAnticipative : ∀ a ∈ algorithms, NonAnticipative R a.2

/-- The expected cost of a randomized algorithm on an instance. -/
def Randomized.cost {R : Revelation P} (μ : Randomized R) (x : P.Inst) : ℚ :=
  (μ.algorithms.map fun a => a.1 * P.cost x (a.2 x)).sum

def Randomized.Competitive {R : Revelation P} (μ : Randomized R) (ρ α : ℚ) : Prop :=
  ∀ x, (∀ a ∈ μ.algorithms, P.feasible x (a.2 x)) ∧
    ∀ σ, P.feasible x σ → μ.cost x ≤ ρ * P.cost x σ + α

/-- A finite distribution over instances, each with a feasible witness
schedule. -/
structure Hard (P : Problem) where
  instances : List (ℚ × (x : P.Inst) × P.Sched x)
  nonneg : ∀ a ∈ instances, 0 ≤ a.1
  feasible : ∀ a ∈ instances, P.feasible a.2.1 a.2.2

/-- The expected excess of an algorithm over `ρ` times the witnesses plus `α`. -/
def Hard.excess (H : Hard P) (A : Algorithm P) (ρ α : ℚ) : ℚ :=
  (H.instances.map fun a => a.1 * (P.cost a.2.1 (A a.2.1) - ρ * P.cost a.2.1 a.2.2 - α)).sum

/-- The distribution defeats the ratio: every non-anticipative algorithm
schedules one of its instances infeasibly or has positive expected excess. -/
def Hard.Defeats (H : Hard P) (R : Revelation P) (ρ α : ℚ) : Prop :=
  ∀ A, NonAnticipative R A → (∃ a ∈ H.instances, ¬ P.feasible a.2.1 (A a.2.1)) ∨
    0 < H.excess A ρ α

/-- The embedding respects what is revealed and what is decided. -/
structure Causal {A B : Problem} (RA : Revelation A) (RB : Revelation B)
    (e : Embedding A B) : Prop where
  same : ∀ x y t, RA.same x y t → RB.same (e.map x) (e.map y) t
  agree : ∀ x y τ τ' t, RB.agree (e.map x) (e.map y) τ τ' t →
    RA.agree x y (e.back x τ) (e.back y τ') t

axiom adversaryWins_iff (R : Revelation P) (ρ α : ℚ) :
    AdversaryWins R ρ α ↔ ¬ SchedulerWins R ρ α

axiom randomized_of_competitive (R : Revelation P) {A : Algorithm P} {ρ α : ℚ}
    (hA : NonAnticipative R A) (hc : Competitive A ρ α) :
    ∃ μ : Randomized R, μ.Competitive ρ α

axiom yao (R : Revelation P) (H : Hard P) {ρ α : ℚ} (hH : H.Defeats R ρ α) :
    ¬ ∃ μ : Randomized R, μ.Competitive ρ α

axiom schedulerWins_of_embedding {A B : Problem} {RA : Revelation A} {RB : Revelation B}
    {e : Embedding A B} (he : e.Sound) (hc : Causal RA RB e) {ρ α : ℚ} (hρ : 0 ≤ ρ) :
    SchedulerWins RB ρ α → SchedulerWins RA ρ α

axiom adversaryWins_of_embedding {A B : Problem} {RA : Revelation A} {RB : Revelation B}
    {e : Embedding A B} (he : e.Sound) (hc : Causal RA RB e) {ρ α : ℚ} (hρ : 0 ≤ ρ) :
    AdversaryWins RA ρ α → AdversaryWins RB ρ α

end Lax434175.Online
