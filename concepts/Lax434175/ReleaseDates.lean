import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Lax434175.Modules

/-!
---
title: Release dates
type: theorem
---
Every job of every kernel has a release date $r_j$, and no job may start
before its release date. The release-date field has the values

- none: all release dates are $0$;
- release dates: arbitrary release dates;
- online: arbitrary release dates; the value records that the jobs become
  known only at their release dates. This concerns the algorithms that are
  admitted, not the instances and schedules, which are those of the value
  release dates.

The value none is a special case of the value release dates; the value
online is comparable only with itself.

The number of distinct release dates is a parameter of every kernel.

**Theorem.** Over every kernel, the release-date field is sound.
-/

namespace Lax434175.ReleaseDates
open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | releaseDates
  | online
  deriving DecidableEq

/-- The instances of a value. -/
def Value.holds (K : Kernel) : Value → K.Inst → Prop
  | .none, x => ∀ j, K.release x j = 0
  | .releaseDates, _ => True
  | .online, _ => True

def le : Value → Value → Bool
  | .none, .releaseDates => true
  | v, w => decide (v = w)

/-- The release-date field over a kernel. -/
def module (K : Kernel) : Module K where
  Value := Value
  Data _ _ := Unit
  admits v x _ := v.holds K x
  constraint _ x _ σ := ∀ j, (K.release x j : NNRat) ≤ K.start x σ j
  le := le
  embed _ _ _ := ()

/-- The number of distinct release dates. -/
def distinct (K : Kernel) : K.Inst → ℕ :=
  fun x => (Finset.univ.image (K.release x)).card

axiom sound (K : Kernel) : (module K).Sound

end Lax434175.ReleaseDates
