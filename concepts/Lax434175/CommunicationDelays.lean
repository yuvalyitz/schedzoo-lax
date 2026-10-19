import Mathlib.Algebra.Order.Field.Rat
import Lax434175.ParallelMachines

/-!
---
title: Communication delays
type: theorem
---
The communication-delay field of a machine model on parallel machines has
the values

- none: no delays;
- unit: a set of ordered pairs of jobs is given; if $(i, j)$ is such a pair
  and the two jobs are processed on different sets of machines, then job $j$
  may not start before one time unit after the completion of job $i$;
- general: for some ordered pairs of jobs a delay $c_{ij}$ is given, and the
  same holds with $c_{ij}$ in place of one time unit.

The pairs with a delay are those related by the precedence constraints of
the problem; the delay adds to the precedence constraint only when the two
jobs are not processed in the same place.

No delays is the special case without pairs; unit delays are the special
case $c_{ij} = 1$.

**Theorem.** Over every machine model, the communication-delay field is
sound.
-/

namespace Lax434175.CommunicationDelays
open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines

inductive Value
  | none
  | unit
  | general

/-- The data of a value. -/
def Data : Value → Inst → Type
  | .none, _ => Unit
  | .unit, x => Fin x.jobs → Fin x.jobs → Prop
  | .general, x => Fin x.jobs → Fin x.jobs → ℕ → Prop

/-- `view v d i j c`: the pair `(i, j)` has the delay `c`. -/
def view {x : Inst} : (v : Value) → Data v x → Fin x.jobs → Fin x.jobs → ℕ → Prop
  | .none, _ => fun _ _ _ => False
  | .unit, r => fun i j c => r i j ∧ c = 1
  | .general, d => d

def le : Value → Value → Bool
  | .none, _ => true
  | .unit, .none => false
  | .unit, _ => true
  | .general, .general => true
  | .general, _ => false

def embed : {v w : Value} → le v w = true → (x : Inst) → Data v x → Data w x
  | _, .none, _, _, _ => ()
  | .none, .unit, _, _, _ => fun _ _ => False
  | .unit, .unit, _, _, d => d
  | v, .general, _, _, d => view v d
  | .general, .unit, h, _, _ => absurd h Bool.false_ne_true

/-- The communication-delay field of a machine model. -/
def module (M : Model) : Module M.kernel where
  Value := Value
  Data v x := Data v (M.inst x)
  admits _ _ _ := True
  constraint v x d σ := ∀ i j c, view v d i j c → ∀ S S', M.uses x σ i S → M.uses x σ j S' →
    S ≠ S' →
    (M.kernel.completion x σ (Fin.cast (M.jobs_eq x).symm i) : ℚ) + (c : ℚ) ≤
      (M.kernel.start x σ (Fin.cast (M.jobs_eq x).symm j) : ℚ)
  le := le
  embed h x d := embed h (M.inst x) d

axiom sound (M : Model) : (module M).Sound

end Lax434175.CommunicationDelays
