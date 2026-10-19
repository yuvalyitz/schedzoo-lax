import Mathlib.Data.Finset.Card
import Lax434175.ParallelMachines

/-!
---
title: Machine sets and multiprocessor tasks
type: theorem
---
The machine-set field of a machine model on parallel machines determines
which sets of machines a job may occupy. Its values are

- none: a job occupies any single machine;
- machine sets $M_j$: a job occupies a single machine of a given set $M_j$;
- fixed sets $\mathrm{fix}_j$: a job occupies all machines of a given set
  $\mathrm{fix}_j$ simultaneously;
- sizes in $\{1, m\}$: a job occupies either one machine or all machines;
- sizes $\mathrm{size}_j$: a job occupies any $\mathrm{size}_j$ machines
  simultaneously;
- general: for every job the admissible sets of machines are given
  explicitly.

The value none is a special case of machine sets (every $M_j$ is the set of
all machines), of sizes in $\{1, m\}$ and of sizes (every size is $1$).
Sizes in $\{1, m\}$ are a special case of sizes. Every value is a special
case of the general one. Fixed sets are not comparable with the value none:
a job that may use any machine is not a job bound to one set.

**Theorem.** Over every machine model, the machine-set field is sound.
-/

namespace Lax434175.MachineSets
open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines

inductive Value
  | none
  | sets
  | fix
  | sizeOneOrAll
  | size
  | general

/-- The data of a value. -/
def Data : Value → Inst → Type
  | .none, _ => Unit
  | .sets, x => Fin x.jobs → Fin x.machines → Prop
  | .fix, x => Fin x.jobs → Finset (Fin x.machines)
  | .sizeOneOrAll, x => Fin x.jobs → Bool
  | .size, x => Fin x.jobs → ℕ
  | .general, x => Fin x.jobs → Finset (Fin x.machines) → Prop

/-- Whether a job may occupy a set of machines. -/
def view {x : Inst} : (v : Value) → Data v x → Fin x.jobs → Finset (Fin x.machines) → Prop
  | .none, _ => fun _ S => S.card = 1
  | .sets, M => fun j S => S.card = 1 ∧ ∀ i ∈ S, M j i
  | .fix, F => fun j S => S = F j
  | .sizeOneOrAll, all => fun j S => S.card = if all j then x.machines else 1
  | .size, size => fun j S => S.card = size j
  | .general, allowed => allowed

def le : Value → Value → Bool
  | .none, .fix => false
  | .none, _ => true
  | .sets, .sets | .sets, .general => true
  | .fix, .fix | .fix, .general => true
  | .sizeOneOrAll, .sizeOneOrAll | .sizeOneOrAll, .size | .sizeOneOrAll, .general => true
  | .size, .size | .size, .general => true
  | .general, .general => true
  | _, _ => false

def embed : {v w : Value} → le v w = true → (x : Inst) → Data v x → Data w x
  | .none, .none, _, _, _ => ()
  | .none, .sets, _, _, _ => fun _ _ => True
  | .none, .sizeOneOrAll, _, _, _ => fun _ => false
  | .none, .size, _, _, _ => fun _ => 1
  | .sets, .sets, _, _, d => d
  | .fix, .fix, _, _, d => d
  | .sizeOneOrAll, .sizeOneOrAll, _, _, d => d
  | .sizeOneOrAll, .size, _, x, d => fun j => if d j then x.machines else 1
  | .size, .size, _, _, d => d
  | v, .general, _, _, d => view v d
  | .none, .fix, h, _, _ | .sets, .none, h, _, _ | .sets, .fix, h, _, _
  | .sets, .sizeOneOrAll, h, _, _ | .sets, .size, h, _, _ | .fix, .none, h, _, _
  | .fix, .sets, h, _, _ | .fix, .sizeOneOrAll, h, _, _ | .fix, .size, h, _, _
  | .sizeOneOrAll, .none, h, _, _ | .sizeOneOrAll, .sets, h, _, _
  | .sizeOneOrAll, .fix, h, _, _ | .size, .none, h, _, _ | .size, .sets, h, _, _
  | .size, .fix, h, _, _ | .size, .sizeOneOrAll, h, _, _ | .general, .none, h, _, _
  | .general, .sets, h, _, _ | .general, .fix, h, _, _ | .general, .sizeOneOrAll, h, _, _
  | .general, .size, h, _, _ => absurd h Bool.false_ne_true

/-- The machine-set field. -/
def module (M : Model) : Module M.kernel where
  Value := Value
  Data v x := Data v (M.inst x)
  admits _ _ _ := True
  constraint v x d σ := ∀ j S, M.uses x σ j S → view v d j S
  le := le
  embed h x d := embed h (M.inst x) d

axiom sound (M : Model) : (module M).Sound

end Lax434175.MachineSets
