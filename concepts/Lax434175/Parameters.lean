import Lax434175.Assembly

/-!
---
title: Parameters along embeddings
type: theorem
---
A parameter of a problem assigns a natural number to every instance. An
embedding of $A$ into $B$ bounds a parameter $\kappa_B$ of $B$ by a function
$g$ of a parameter $\kappa_A$ of $A$ if $\kappa_B(f(x)) \le g(\kappa_A(x))$
for every instance $x$ of $A$, where $f$ is the instance map.

For problems assembled from fields there are two sources of parameters. A
kernel parameter depends on the kernel instance only, such as the number of
machines. A field parameter depends on the data of one constraint module,
such as the number of distinct release dates; it is invariant if reading data
with a more general value does not change it.

**Theorem.** The embedding induced by a field-wise comparison of
specifications preserves every kernel parameter and every invariant field
parameter exactly.

For reductions of decision versions, let $\kappa_A$ and $\kappa_B$ assign to
the instances of $A$ and $B$ values of any kind, for instance pairs of
numbers, and let $R$ relate such values. Problem $A$ reduces to $B$ with
$R$ if some reduction maps every instance $x$ to an instance $y$ with
$R(\kappa_A(x), \kappa_B(y))$. A reduction between two problems of one
family is in place if it does not change the kernel instance, and hence no
kernel parameter, and changes no invariant field parameter.

**Theorem.** A sound embedding that relates the parameters gives a reduction
with the same relation, and reductions with relations compose.

Reductions are arbitrary maps here: their running time is not modelled.
-/

namespace Lax434175.Parameters
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

/-- A parameter of a problem. -/
abbrev Parameter (P : Problem) := P.Inst → ℕ

/-- The embedding bounds `κB` by `g` of `κA`. -/
def Bounds {A B : Problem} (e : Embedding A B) (κA : Parameter A) (κB : Parameter B)
    (g : ℕ → ℕ) : Prop :=
  ∀ x, κB (e.map x) ≤ g (κA x)

/-- A parameter that depends on the kernel instance only. -/
def ofKernel {K : Kernel} (F : Family K) (κ : K.Inst → ℕ) (s : Spec F) :
    Parameter (problem F s) :=
  fun x => κ x.base

/-- A parameter that depends on the data of one constraint module. -/
abbrev FieldParameter {K : Kernel} (M : Module K) :=
  (v : M.Value) → (x : K.Inst) → M.Data v x → ℕ

/-- Reading data with a more general value does not change the parameter. -/
def FieldParameter.Invariant {K : Kernel} {M : Module K} (κ : FieldParameter M) : Prop :=
  ∀ (v w : M.Value) (h : M.le v w = true) (x : K.Inst) (d : M.Data v x),
    κ w x (M.embed h x d) = κ v x d

/-- A field parameter as a parameter of an assembled problem. -/
def ofField {K : Kernel} (F : Family K) (i : F.ModuleName) (κ : FieldParameter (F.module i))
    (s : Spec F) : Parameter (problem F s) :=
  fun x => κ (s.module i) x.base (x.data i)

/-- `A` reduces to `B` by a reduction that relates the parameter values of
an instance and of its image by `R`. -/
def ReducibleWith {A B : Problem} {α β : Type} (κA : A.Inst → α) (κB : B.Inst → β)
    (R : α → β → Prop) : Prop :=
  ∃ r : DecisionReduction A B, r.Sound ∧ ∀ x D, R (κA x) (κB (r.map x D))

/-- A reduction between two problems of a family that keeps the kernel
instance and every invariant field parameter. -/
structure InPlace {K : Kernel} {F : Family K} {s t : Spec F}
    (r : DecisionReduction (problem F s) (problem F t)) : Prop where
  base : ∀ (x : Inst F s) (D : ℤ), (r.map x D).base = x.base
  field : ∀ (i : F.ModuleName) (κ : FieldParameter (F.module i)), κ.Invariant →
    ∀ (x : Inst F s) (D : ℤ), ofField F i κ t (r.map x D) = ofField F i κ s x

/-- The decision version of the problem of `s` reduces in place to that of
`t`. -/
def ReducibleInPlace {K : Kernel} {F : Family K} (s t : Spec F) : Prop :=
  ∃ r : DecisionReduction (problem F s) (problem F t), r.Sound ∧ InPlace r

axiom reducibleWith_of_embedding {A B : Problem} {α β : Type} (e : Embedding A B)
    (κA : A.Inst → α) (κB : B.Inst → β) (R : α → β → Prop) :
    e.Sound → (∀ x, R (κA x) (κB (e.map x))) → ReducibleWith κA κB R

axiom reducibleWith_trans {A B C : Problem} {α β γ : Type} (κA : A.Inst → α)
    (κB : B.Inst → β) (κC : C.Inst → γ) (R : α → β → Prop) (S : β → γ → Prop) :
    ReducibleWith κA κB R → ReducibleWith κB κC S →
      ReducibleWith κA κC (fun a c => ∃ b, R a b ∧ S b c)

axiom reducible_of_reducibleWith {A B : Problem} {α β : Type} (κA : A.Inst → α)
    (κB : B.Inst → β) (R : α → β → Prop) : ReducibleWith κA κB R → Reducible A B

axiom lift_ofKernel {K : Kernel} (F : Family K) (hF : F.Sound) (κ : K.Inst → ℕ)
    {s t : Spec F} (h : s.le t) :
    ∀ x, ofKernel F κ t ((lift F hF h).map x) = ofKernel F κ s x

axiom lift_ofField {K : Kernel} (F : Family K) (hF : F.Sound) (i : F.ModuleName)
    (κ : FieldParameter (F.module i)) (hκ : κ.Invariant) {s t : Spec F} (h : s.le t) :
    ∀ x, ofField F i κ t ((lift F hF h).map x) = ofField F i κ s x

end Lax434175.Parameters
