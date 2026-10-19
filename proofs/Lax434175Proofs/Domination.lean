import Mathlib.Tactic
import Lax434175.Domination
import Lax434175Proofs.Propagation

namespace Lax434175Proofs.Domination
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters
open Lax434175.Domination Lax434175Proofs.Propagation
open Lax496464.WH_A2_FptReductions

variable {P : Problem} {R : PReading P} {κ κ' : TParameter P} {g : ℕ → ℕ}

/-- The words with `κ ≤ k` have `κ' ≤ g(0) + ⋯ + g(k)`. -/
theorem upto_dominated (h : Dominated κ' κ g) {k : ℕ} {u : List ℕ} (hu : u ∈ Upto R κ k) :
    u ∈ Upto R κ' (gsum g k) := by
  obtain ⟨x, D, hx, hk⟩ := hu
  exact ⟨x, D, hx, (h x D).trans (Lax434175Proofs.ResultTransfer.le_sum g hk)⟩

/-- The identity on words is an fpt-reduction from `κ` to `κ'`: the words, the
answers and the chosen instance of a word are the same for both. -/
theorem id_fptReduces (hg : Computable g) (h : Dominated κ' κ g) :
    parameterized R κ ≤ᶠᵖᵗ parameterized R κ' := by
  refine ⟨fun u => u, ⟨⟨fun u hu => hu, fun u _ => Iff.rfl⟩, ⟨g, hg, fun u hu => ?_⟩,
    Lax496464.WH_A4_MachineFacts.fptTimeOn_id _ _⟩⟩
  have e1 : (parameterized R κ').param u = κ' hu.choose hu.choose_spec.choose := by
    unfold parameterized; exact dif_pos hu
  have e2 : (parameterized R κ).param u = κ hu.choose hu.choose_spec.choose := by
    unfold parameterized; exact dif_pos hu
  rw [e1, e2]
  exact h _ _

/--
---
conclusion: Lax434175.Domination.paraNPHard_of_dominated
---
The same reductions, into more words.
-/
theorem paraNPHard_of_dominated (h : Dominated κ' κ g) : ParaNPHard R κ → ParaNPHard R κ' := by
  rintro ⟨k, H⟩
  refine ⟨gsum g k, fun A hA => ?_⟩
  obtain ⟨f, hf, hfx⟩ := H A hA
  exact ⟨f, hf, fun a => ⟨⟨(hfx a).1.1, upto_dominated h (hfx a).1.2⟩, (hfx a).2⟩⟩

/--
---
conclusion: Lax434175.Domination.wHard_of_dominated
---
-/
theorem wHard_of_dominated (t : ℕ) (hg : Computable g) (h : Dominated κ' κ g) :
    WHard R t κ → WHard R t κ' := fun H =>
  Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces H (id_fptReduces hg h)

/--
---
conclusion: Lax434175.Domination.inPFixed_of_dominated
---
The same program, on fewer words.
-/
theorem inPFixed_of_dominated (h : Dominated κ' κ g) : InPFixed R κ' → InPFixed R κ := by
  intro H k
  obtain ⟨p, c, d, hp⟩ := H (gsum g k)
  exact ⟨p, c, d, computes_restrict (D := (restrict (decision R) (Upto R κ' (gsum g k))).Domain)
    (fun u hu => ⟨hu.1, upto_dominated h hu.2⟩) (fun _ _ => rfl) hp⟩

/--
---
conclusion: Lax434175.Domination.isFPT_of_dominated
---
-/
theorem isFPT_of_dominated (hg : Computable g) (h : Dominated κ' κ g)
    (hp : IsParameterized (parameterized R κ)) : IsFPT R κ' → IsFPT R κ := fun H =>
  Lax496464.WH_A3_ReductionCalculus.mem_FPT_of_fptReduces hp (id_fptReduces hg h) H

/--
---
conclusion: Lax434175.Domination.left_tplus
---
-/
theorem left_tplus (κ κ' : TParameter P) : Dominated κ (tplus κ κ') id :=
  fun _ _ => Nat.le_add_right _ _

/--
---
conclusion: Lax434175.Domination.right_tplus
---
-/
theorem right_tplus (κ κ' : TParameter P) : Dominated κ' (tplus κ κ') id :=
  fun _ _ => Nat.le_add_left _ _

/--
---
conclusion: Lax434175.Domination.ops_numP_pmax
---
The distinct processing times lie in `{0, …, p_max}`.
-/
theorem ops_numP_pmax (s : Assembly.Spec OperationsFamily.family) :
    Dominated (lift (Ops.numP s)) (lift (Ops.pmax s)) (· + 1) := by
  intro x _
  show (Finset.univ.image fun o : Operations.Op x.base => Operations.opTime x.base o).card ≤
    (Finset.univ.sup fun o : Operations.Op x.base => Operations.opTime x.base o) + 1
  calc _ ≤ (Finset.range ((Finset.univ.sup fun o : Operations.Op x.base =>
        Operations.opTime x.base o) + 1)).card := by
        refine Finset.card_le_card fun v hv => ?_
        obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ o)))
    _ = _ := Finset.card_range _

end Lax434175Proofs.Domination
