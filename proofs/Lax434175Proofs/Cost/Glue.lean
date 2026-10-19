import Mathlib.Tactic
import Lax434175.Results
import Lax808846Proofs.Transfer

/-!
From a program in IMP+ to an exact running time.

A contributor writes an algorithm as an IMP+ command and proves, with the
reasoning rules of lax-808846, that on the tape `|u| :: u` of every word `u` of an
instance with a threshold it writes the answer for that instance, at a cost `K` and with values
below `B` (`Solves`). If the compiled cost `10 K + 1` is at most `a (T(x) + 1)`
and the values fit in words of `a` times the logarithm of the input, the
algorithm decides the problem within `O(T)`.
-/

namespace Lax434175Proofs.Cost
open Lax434175.Problems Lax434175.Results
open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer

variable {P : Problem} (R : PReading P)

/-- The tapes of the words of instances with a threshold. -/
def Tapes : Set (List ℕ) := {v | ∃ u x D, EncodesDecision R u x D ∧ v = u.length :: u}

/-- A command solving the problem on the tapes, restricted to one tape. -/
theorem solves_single {L : Layout} {c : Com} {D : Set (List ℕ)} {f : List ℕ → List ℕ}
    {B K : List ℕ → ℕ} (h : Solves L c D f B K) {v : List ℕ} (hv : v ∈ D) :
    Solves L c {v} f B K :=
  ⟨h.ok, fun y hy => h.inp y (by rw [Set.mem_singleton_iff.mp hy]; exact hv),
    fun y hy => h.run y (by rw [Set.mem_singleton_iff.mp hy]; exact hv)⟩

/-- **Glue.** An IMP+ command solving the decision version on the tapes, with
cost and value bounds as above, decides it within `O(T)`. -/
theorem decidesWithin_of_solves {T : P.Inst → ℕ} {L : Layout} {c : Com} {B K : List ℕ → ℕ}
    {f : List ℕ → List ℕ} (h : Solves L c (Tapes R) f B K)
    (hf : ∀ u x D, EncodesDecision R u x D → f (u.length :: u) = verdict x D) (a : ℕ)
    (hK : ∀ u x D, EncodesDecision R u x D → L.const * K (u.length :: u) + 1 ≤ a * (T x + 1))
    (hB : ∀ u x D, EncodesDecision R u x D → ∀ ℓ, WordOk a u ℓ →
      1 < B (u.length :: u) ∧ max (B (u.length :: u)) (L.span (B (u.length :: u))) ≤ 2 ^ ℓ) :
    DecidesWithin R T := by
  refine ⟨compileProgram L c, a, fun u x D hx ℓ hℓ => ?_⟩
  have hv : u.length :: u ∈ Tapes R := ⟨u, x, D, hx, rfl⟩
  obtain ⟨h1, hmax⟩ := hB u x D hx ℓ hℓ
  have hc := computesInTime_of_solves (T := fun _ => a * (T x + 1)) (w := ℓ) (solves_single h hv)
    (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact fitsWords_of_max_le h1 hmax)
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hK u x D hx)
  obtain ⟨t, ht, hrun⟩ := hc (u.length :: u) (Set.mem_singleton _)
  exact ⟨t, ht, hf u x D hx ▸ hrun⟩

/-- **Exact glue.** The same command decides within exactly `L.const K + 1` compiled
instructions, for any bound `T x D` above it: no constant is hidden. -/
theorem decidesExact_of_solves {T : P.Inst → ℤ → ℕ} {L : Layout} {c : Com} {B K : List ℕ → ℕ}
    {f : List ℕ → List ℕ} (h : Solves L c (Tapes R) f B K)
    (hf : ∀ u x D, EncodesDecision R u x D → f (u.length :: u) = verdict x D) (a : ℕ)
    (hK : ∀ u x D, EncodesDecision R u x D → L.const * K (u.length :: u) + 1 ≤ T x D)
    (hB : ∀ u x D, EncodesDecision R u x D → ∀ ℓ, WordOk a u ℓ →
      1 < B (u.length :: u) ∧ max (B (u.length :: u)) (L.span (B (u.length :: u))) ≤ 2 ^ ℓ) :
    DecidesExact R T := by
  refine ⟨compileProgram L c, a, fun u x D hx ℓ hℓ => ?_⟩
  have hv : u.length :: u ∈ Tapes R := ⟨u, x, D, hx, rfl⟩
  obtain ⟨h1, hmax⟩ := hB u x D hx ℓ hℓ
  have hc := computesInTime_of_solves (T := fun _ => T x D) (w := ℓ) (solves_single h hv)
    (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact fitsWords_of_max_le h1 hmax)
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hK u x D hx)
  obtain ⟨t, ht, hrun⟩ := hc (u.length :: u) (Set.mem_singleton _)
  exact ⟨t, ht, hf u x D hx ▸ hrun⟩

end Lax434175Proofs.Cost
