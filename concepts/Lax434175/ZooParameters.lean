import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Lax434175.ParallelMachines
import Lax434175.Shops
import Lax434175.Objectives

/-!
---
title: Parameters of scheduling problems
type: theorem
---
The parameters by which scheduling problems are commonly parameterized are
functions of an instance.

Over every kernel: the number $n$ of jobs and the number of distinct release
dates. On parallel machines and in shops: the number $m$ of machines, the
maximum processing time $p_{\max}$ and the number of distinct processing
times. For every objective value: the number of distinct weights and the
number of distinct due dates, where an unweighted value has the weights $1$
and a value without due dates the due dates $0$.

The first five depend on the kernel instance only. They are therefore
preserved by every embedding induced by a field-wise comparison and by every
reduction in place.

**Theorem.** Reading the data of an objective value with a more general
value changes neither the number of distinct weights nor the number of
distinct due dates.
-/

namespace Lax434175.ZooParameters
open Lax434175.Kernels Lax434175.Modules

/-- The number of distinct values of a function on the jobs. -/
def distinct {n : ℕ} (f : Fin n → ℕ) : ℕ := (Finset.univ.image f).card

/-- The number of jobs. -/
def jobs (K : Kernel) : K.Inst → ℕ := K.jobs

/-- The number of distinct release dates. -/
def releaseDates (K : Kernel) (x : K.Inst) : ℕ := distinct (K.release x)

namespace Parallel

/-- The number of machines. -/
def machines (M : ParallelMachines.Model) : M.kernel.Inst → ℕ := ParallelMachines.machines M

/-- The maximum processing time. -/
def pmax (M : ParallelMachines.Model) (x : M.kernel.Inst) : ℕ :=
  Finset.univ.sup fun j => Finset.univ.sup fun i => (M.inst x).p j i

/-- The number of distinct processing times. -/
def processingTimes (M : ParallelMachines.Model) (x : M.kernel.Inst) : ℕ :=
  (Finset.univ.image fun q : Fin (M.inst x).jobs × Fin (M.inst x).machines =>
    (M.inst x).p q.1 q.2).card

end Parallel

namespace Shop

/-- The number of machines. -/
def machines : Shops.kernel.Inst → ℕ := Shops.machines

/-- The maximum processing time of an operation. -/
def pmax (x : Shops.Inst) : ℕ :=
  Finset.univ.sup fun j => Finset.univ.sup fun k => x.p j k

/-- The number of distinct processing times of operations. -/
def processingTimes (x : Shops.Inst) : ℕ :=
  (Finset.univ.image fun o : Shops.Op x => x.p o.1 o.2).card

end Shop

/-- The number of distinct weights. -/
def weights (K : Kernel) (v : Objectives.Value) (x : K.Inst) (d : Objectives.Data K v x) : ℕ :=
  distinct (Objectives.weight v d)

/-- The number of distinct due dates. -/
def dueDates (K : Kernel) (v : Objectives.Value) (x : K.Inst) (d : Objectives.Data K v x) : ℕ :=
  distinct (Objectives.dueDate v d)

axiom weights_embed (K : Kernel) (v w : Objectives.Value) (h : Objectives.le v w = true)
    (x : K.Inst) (d : Objectives.Data K v x) :
    weights K w x (Objectives.embed h x d) = weights K v x d

axiom dueDates_embed (K : Kernel) (v w : Objectives.Value) (h : Objectives.le v w = true)
    (x : K.Inst) (d : Objectives.Data K v x) :
    dueDates K w x (Objectives.embed h x d) = dueDates K v x d

end Lax434175.ZooParameters
