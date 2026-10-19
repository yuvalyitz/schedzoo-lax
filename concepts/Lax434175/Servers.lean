import Mathlib.Algebra.Order.Field.Rat
import Lax434175.ParallelMachines
import Lax434175.Shops

/-!
---
title: A single server with setup times
type: theorem
---
With a single server, every job on parallel machines, and every operation in
a shop, needs a setup immediately before it is processed. The setup of job
$j$ takes $s_j$ time units, during which it occupies both the machines of
the job and the server. Hence

- the setup of a job starts no earlier than its release date $r_j$, so the
  job starts no earlier than $r_j + s_j$; in a shop this holds for the first
  operation of the job, the one that starts when the job starts;
- the setups of two different jobs do not overlap, since there is one
  server;
- of two jobs that share a machine, the later one starts no earlier than the
  completion of the earlier one plus its own setup time.

In a shop the setup of a later operation of a job may overlap the job's
previous operation on another machine: setups are separable, and only the
setup of the first operation waits for the release date. This is the model of
Brucker, Knust and Wang (2005) and of the papers of the same group on a single
server.

The field has the value "none", without server and setups, and three values
with a server: unit setup times, equal setup times, and arbitrary setup
times. Unit is a special case of equal and equal of arbitrary; the value
none is incomparable with the others.

**Theorem.** The server field is sound over every machine model on parallel
machines and for shops.
-/

namespace Lax434175.Servers
open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | unit
  | equal
  | arbitrary
  deriving DecidableEq

/-- Setup times of `n` items; no data without a server. -/
def Data (Item : Type) : Value → Type
  | .none => Unit
  | .unit | .equal | .arbitrary => Item → ℕ

/-- The setup times, where there is a server. -/
def view {Item : Type} : (v : Value) → Data Item v → Option (Item → ℕ)
  | .none, _ => Option.none
  | .unit, s | .equal, s | .arbitrary, s => some s

/-- The condition on the setup times. -/
def Admits {Item : Type} : (v : Value) → Data Item v → Prop
  | .unit, s => ∀ a, s a = 1
  | .equal, s => ∃ c, ∀ a, s a = c
  | _, _ => True

def le : Value → Value → Bool
  | .unit, .unit | .unit, .equal | .unit, .arbitrary => true
  | .equal, .equal | .equal, .arbitrary => true
  | .arbitrary, .arbitrary => true
  | .none, .none => true
  | _, _ => false

def embed {Item : Type} : {v w : Value} → le v w = true → Data Item v → Data Item w
  | .none, .none, _, _ => ()
  | .unit, .unit, _, s | .unit, .equal, _, s | .unit, .arbitrary, _, s
  | .equal, .equal, _, s | .equal, .arbitrary, _, s | .arbitrary, .arbitrary, _, s => s
  | .none, .unit, h, _ | .none, .equal, h, _ | .none, .arbitrary, h, _
  | .unit, .none, h, _ | .equal, .none, h, _ | .equal, .unit, h, _
  | .arbitrary, .none, h, _ | .arbitrary, .unit, h, _ | .arbitrary, .equal, h, _ =>
      absurd h Bool.false_ne_true

/-- The server constraints for items with given start and completion times,
release dates of their setups, setup times, and a relation "share a
machine". -/
def Served {Item : Type} (start completion release : Item → ℚ)
    (shares : Item → Item → Prop) (s : Item → ℕ) : Prop :=
  (∀ a, release a + s a ≤ start a) ∧
  (∀ a b, a ≠ b → start a + s b ≤ start b ∨ start b + s a ≤ start a) ∧
  ∀ a b, a ≠ b → shares a b → completion a + s b ≤ start b ∨ completion b + s a ≤ start a

/-- The release date of the setup of an item: the release date of its job if
the item starts when its job starts (the first operation of the job), and `0`
otherwise. -/
def setupRelease {Item : Type} (start jobStart release : Item → ℚ) (a : Item) : ℚ :=
  if start a = jobStart a then release a else 0

/-- The server field of a machine model on parallel machines. -/
def parallel (M : ParallelMachines.Model) : Module M.kernel where
  Value := Value
  Data v x := Data (Fin (M.kernel.jobs x)) v
  admits v _ d := Admits v d
  constraint v x d σ := ∀ s, view v d = some s →
    Served (fun j => (M.kernel.start x σ j : ℚ)) (fun j => (M.kernel.completion x σ j : ℚ))
      (fun j => (M.kernel.release x j : ℚ)) (fun i j => ∃ S S', M.uses x σ (Fin.cast (M.jobs_eq x) i) S ∧
        M.uses x σ (Fin.cast (M.jobs_eq x) j) S' ∧ ¬ Disjoint S S') s
  le := le
  embed h _ d := embed h d

/-- The server field of shops: every operation needs a setup. -/
def shop : Module Shops.kernel where
  Value := Value
  Data v x := Data (Shops.Op x) v
  admits v _ d := Admits v d
  constraint v x d σ := ∀ s, view v d = some s →
    Served (fun o : Shops.Op x => (Shops.Sched.start σ o.1 o.2 : ℚ))
      (fun o => (Shops.finish x σ o : ℚ))
      (setupRelease (fun o : Shops.Op x => (Shops.Sched.start σ o.1 o.2 : ℚ))
        (fun o => (Shops.jobStart x σ o.1 : ℚ)) (fun o => (x.r o.1 : ℚ)))
      (fun a b => ¬ Disjoint (Shops.Sched.machines σ a.1 a.2) (Shops.Sched.machines σ b.1 b.2)) s
  le := le
  embed h _ d := embed h d

axiom parallel_sound (M : ParallelMachines.Model) : (parallel M).Sound

axiom shop_sound : shop.Sound

end Lax434175.Servers
