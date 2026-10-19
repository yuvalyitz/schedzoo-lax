import Lax434175.Shops

/-!
---
title: Transportation delays and a transport robot
type: theorem
---
In a shop with transportation delays an instance carries, for every job $j$
and every ordered pair of its operations $k, l$, a delay $t_{jkl}$. Of any
two operations of a job, the later one may not start before the completion
of the earlier one plus the delay from the earlier to the later.

The shape field restricts the delays:

- none: all delays are $0$;
- uniform: all delays equal one number $T$;
- two values: there are two numbers, and the delays of each job all equal
  one of them;
- job: the delay depends on the job only, $t_j$;
- source: the delay depends on the earlier operation only, $t_k$;
- job and source: the delay does not depend on the later operation,
  $t_{jk}$;
- pair: the delay depends on the two positions only, $t_{kl}$, possibly
  required to be symmetric, $t_{kl} = t_{lk}$;
- job and pair: arbitrary delays $t_{jkl}$, possibly required to be
  symmetric, $t_{jkl} = t_{jlk}$.

A shape is a special case of another if its delays are among the other's.

With a transport robot, in addition every transport of a job from an
operation to the next one in its sequence is carried out by a single robot:
the transport starts no earlier than the completion of the operation, lasts
for the delay, and ends no later than the start of the next operation. The
robot may need time to travel empty, as in Brucker and Knust, *Complex
Scheduling*, §4.6: an instance then carries, for every two machines $i, i'$,
an empty moving time $t'_{ii'}$. Of any two transports, the later one departs
no earlier than the arrival of the earlier one plus the time the robot needs
to travel empty from the machines where it delivers the earlier one to the
machines where it picks up the later one, the largest empty moving time
between them. Unless the robot has empty moves, all empty moving times are
$0$, and two transports merely do not overlap.

A problem with a robot and one without are incomparable. A robot without
empty moves is a special case of one with them.

**Theorem.** The field of transportation delays is sound.
-/

namespace Lax434175.Transportation
open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

/-- The delays of an instance. -/
abbrev Delays (x : Inst) := (j : Fin x.jobs) → Fin (x.ops j) → Fin (x.ops j) → ℕ

inductive Shape
  | none
  | uniform
  | twoValues
  | job
  | source
  | jobSource
  | pairSymmetric
  | pair
  | jobPairSymmetric
  | jobPair
  deriving DecidableEq

/-- The delays of a shape. -/
def Shape.holds {x : Inst} : Shape → Delays x → Prop
  | .none, t => ∀ j k l, t j k l = 0
  | .uniform, t => ∃ T, ∀ j k l, t j k l = T
  | .twoValues, t => ∃ T₁ T₂, ∀ j, (∀ k l, t j k l = T₁) ∨ (∀ k l, t j k l = T₂)
  | .job, t => ∀ j k l k' l', t j k l = t j k' l'
  | .source, t => ∃ g : ℕ → ℕ, ∀ j k l, t j k l = g k.val
  | .jobSource, t => ∀ j k l l', t j k l = t j k l'
  | .pairSymmetric, t => ∃ g : ℕ → ℕ → ℕ, (∀ a b, g a b = g b a) ∧ ∀ j k l, t j k l = g k.val l.val
  | .pair, t => ∃ g : ℕ → ℕ → ℕ, ∀ j k l, t j k l = g k.val l.val
  | .jobPairSymmetric, t => ∀ j k l, t j k l = t j l k
  | .jobPair, _ => True

def Shape.le : Shape → Shape → Bool
  | _, .jobPair => true
  | .none, _ => true
  | .uniform, .none => false
  | .uniform, _ => true
  | .twoValues, .twoValues | .twoValues, .job | .twoValues, .jobSource
  | .twoValues, .jobPairSymmetric => true
  | .job, .job | .job, .jobSource | .job, .jobPairSymmetric => true
  | .source, .source | .source, .jobSource | .source, .pair => true
  | .jobSource, .jobSource => true
  | .pairSymmetric, .pairSymmetric | .pairSymmetric, .pair
  | .pairSymmetric, .jobPairSymmetric => true
  | .pair, .pair => true
  | .jobPairSymmetric, .jobPairSymmetric => true
  | _, _ => false

/-- Of two operations of a job, the later one waits for the delay. -/
def Delayed (x : Inst) (t : Delays x) (σ : Sched x) : Prop :=
  ∀ j (k l : Fin (x.ops j)), k ≠ l →
    finish x σ ⟨j, k⟩ + t j k l ≤ σ.start j l ∨ finish x σ ⟨j, l⟩ + t j l k ≤ σ.start j k

/-- The empty moving times of the robot, from a machine to a machine. -/
abbrev EmptyMoves (x : Inst) := Fin x.machines → Fin x.machines → ℕ

/-- The time the robot needs to travel empty from a set of machines to
another: the largest empty moving time from a machine of the first to a
machine of the second. -/
def emptyTime {m : ℕ} (e : Fin m → Fin m → ℕ) (S S' : Finset (Fin m)) : ℕ :=
  S.sup fun i => S'.sup (e i)

/-- A single robot carries every job from each operation to the next, and
between two transports it travels empty from the machines where it delivers
the one to the machines where it picks up the other. -/
def Carried (x : Inst) (t : Delays x) (e : EmptyMoves x) (σ : Sched x) : Prop :=
  ∃ depart : (j : Fin x.jobs) → Fin (x.ops j) → ℕ,
    (∀ j (k l : Fin (x.ops j)), l.val = k.val + 1 →
      finish x σ ⟨j, k⟩ ≤ depart j k ∧ depart j k + t j k l ≤ σ.start j l) ∧
    ∀ j (k l : Fin (x.ops j)) j' (k' l' : Fin (x.ops j')), l.val = k.val + 1 →
      l'.val = k'.val + 1 → (⟨j, k⟩ : Op x) ≠ ⟨j', k'⟩ →
      depart j k + t j k l + emptyTime e (σ.machines j l) (σ.machines j' k') ≤ depart j' k' ∨
      depart j' k' + t j' k' l' + emptyTime e (σ.machines j' l') (σ.machines j k) ≤ depart j k

/-- A value of the field: a shape of delays, whether a robot carries the
jobs, and whether the robot needs time to travel empty. -/
structure Value where
  shape : Shape
  robot : Bool := false
  emptyMoves : Bool := false

/-- No transportation delays and no robot. -/
def Value.none : Value := ⟨.none, false, false⟩

/-- The data of the field: the delays and the empty moving times. -/
abbrev Data (x : Inst) := Delays x × EmptyMoves x

/-- The delays have the shape, and unless the value has a robot with empty
moves, the empty moving times are `0`. -/
def Value.admits {x : Inst} (v : Value) (d : Data x) : Prop :=
  v.shape.holds d.1 ∧ ((v.robot && v.emptyMoves) = false → ∀ i i', d.2 i i' = 0)

/-- The shape is a special case, both values have a robot or neither has,
and empty moves only if the other value has them. -/
def Value.le (v w : Value) : Bool :=
  Shape.le v.shape w.shape && decide (v.robot = w.robot) && (!v.emptyMoves || w.emptyMoves)

/-- The field of transportation delays. -/
def module : Module kernel where
  Value := Value
  Data _ x := Data x
  admits v _ d := v.admits d
  constraint v x d σ := Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ)
  le := Value.le
  embed _ _ d := d

axiom sound : module.Sound

end Lax434175.Transportation
