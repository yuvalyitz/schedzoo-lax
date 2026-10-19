import Mathlib.Tactic
import Lax434175.Bounded
import Lax434175Proofs.Encodings

namespace Lax434175Proofs.Bounded
open Lax434175 Lax434175.Problems Lax434175.Bounded Lax434175.Assembly
open Lax434175.ParallelMachines Lax434175.ParallelProblems Lax434175.Encodings
open Lax434175Proofs.Encodings

/--
---
conclusion: Lax434175.Bounded.bounded_specialCase
---
The inclusion of the instances within the bounds; schedules, feasibility and
costs are those of the problem.
-/
theorem bounded_specialCase (P : Problem) (bs : List (Bound P)) : SpecialCase (bounded P bs) P :=
  ⟨P.inclusion (holds bs), ⟨fun _ _ h => h, fun _ _ _ => le_rfl, fun _ _ h => h, fun _ _ _ => le_rfl⟩⟩

/--
---
conclusion: Lax434175.Bounded.bounded_mono
---
The same embedding, on the instances within the bounds.
-/
theorem bounded_mono {A B : Problem} (e : Embedding A B) (he : e.Sound)
    (bs : List (Bound A)) (cs : List (Bound B)) (h : ∀ x, holds bs x → holds cs (e.map x)) :
    SpecialCase (bounded A bs) (bounded B cs) :=
  ⟨{ map := fun x => ⟨e.map x.1, h x.1 x.2⟩
     forth := fun x σ => e.forth x.1 σ
     back := fun x τ => e.back x.1 τ },
   ⟨fun x σ hσ => he.forth_feasible x.1 σ hσ, fun x σ hσ => he.forth_cost x.1 σ hσ,
    fun x τ hτ => he.back_feasible x.1 τ hτ, fun x τ hτ => he.back_cost x.1 τ hτ⟩⟩

/--
---
conclusion: Lax434175.Bounded.specialCase_bounded
---
-/
theorem specialCase_bounded {A B : Problem} (e : Embedding A B) (he : e.Sound)
    (cs : List (Bound B)) (h : ∀ x, holds cs (e.map x)) : SpecialCase A (bounded B cs) :=
  ⟨{ map := fun x => ⟨e.map x, h x⟩
     forth := fun x σ => e.forth x σ
     back := fun x τ => e.back x τ },
   ⟨fun x σ hσ => he.forth_feasible x σ hσ, fun x σ hσ => he.forth_cost x σ hσ,
    fun x τ hτ => he.back_feasible x τ hτ, fun x τ hτ => he.back_cost x τ hτ⟩⟩

/--
---
conclusion: Lax434175.Bounded.weightedJustInTime_zeroSlack
---
The encoding sets `r_j = d_j - p_j`, so `d_j - r_j - p_j` is `0` for every job.
-/
theorem weightedJustInTime_zeroSlack :
    SpecialCase (problem nonpreemptive (single .sumWZ)) zeroSlackWeightedLate := by
  refine specialCase_bounded weightedJustInTime weightedJustInTime_sound _ fun x b hb => ?_
  simp only [List.mem_singleton] at hb
  subst hb
  change dueSlack (singleRelease .sumWU) (encodeWeighted x) ≤ 0
  unfold dueSlack
  refine Finset.sup_le fun j _ => ?_
  show x.objectiveData.2 j - (x.objectiveData.2 j - need x.base j) - need x.base j ≤ 0
  omega

end Lax434175Proofs.Bounded
