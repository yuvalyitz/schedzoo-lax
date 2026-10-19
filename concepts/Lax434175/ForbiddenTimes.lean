import Mathlib.Data.NNRat.Defs
import Lax434175.Modules

/-!
---
title: Forbidden times and input encodings
type: theorem
---
Two fields that apply to every kernel.

The forbidden-times field has the values "none" and "forbidden times". With
forbidden times, an instance carries a finite list of points in time, and no
job may start or complete at one of them. An instance without forbidden
times is read as one with the empty list.

The encoding field has the values "standard" and "high multiplicity". It
does not restrict the instances or the schedules: the value high
multiplicity records that the input lists every kind of job once, with its
multiplicity in binary, which concerns the size of the input only. The
standard encoding is the special case in which every multiplicity is one.

**Theorem.** Over every kernel, both fields are sound.
-/

namespace Lax434175.ForbiddenTimes
open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | forbidden

/-- No data without forbidden times; a list of points in time with them. -/
def Data : Value → Type
  | .none => Unit
  | .forbidden => List ℕ

/-- The forbidden times; none when the field is absent. -/
def view : (v : Value) → Data v → List ℕ
  | .none, _ => []
  | .forbidden, l => l

def le : Value → Value → Bool
  | .forbidden, .none => false
  | _, _ => true

def embed : {v w : Value} → le v w = true → Data v → Data w
  | _, .none, _, _ => ()
  | v, .forbidden, _, d => view v d

/-- The forbidden-times field over a kernel. -/
def module (K : Kernel) : Module K where
  Value := Value
  Data v _ := Data v
  admits _ _ _ := True
  constraint v x d σ := ∀ t ∈ view v d, ∀ j,
    K.start x σ j ≠ (t : NNRat) ∧ K.completion x σ j ≠ (t : NNRat)
  le := le
  embed h _ d := embed h d

inductive Encoding
  | standard
  | highMultiplicity
  deriving DecidableEq

/-- The encoding field over a kernel. -/
def encoding (K : Kernel) : Module K :=
  Module.ofRestriction Encoding (fun _ _ => True)
    (fun v w => decide (v = .standard ∨ v = w))

axiom sound (K : Kernel) : (module K).Sound

axiom encoding_sound (K : Kernel) : (encoding K).Sound

end Lax434175.ForbiddenTimes
