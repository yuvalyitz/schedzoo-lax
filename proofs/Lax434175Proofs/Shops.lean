import Lax434175.Shops

namespace Lax434175Proofs.Shops
open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

/-- A more special shop type has fewer instances. -/
theorem shopType_holds_mono (v w : ShopType) (h : ShopType.le v w = true) (x : Inst) :
    v.holds x → w.holds x := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | exact hv
    | exact trivial

/--
---
conclusion: Lax434175.Shops.shopType_sound
---
-/
theorem shopType_sound : shopType.Sound where
  admits := fun (v w : ShopType) h x _ hv => shopType_holds_mono v w h x hv
  constraint := fun (v w : ShopType) h x _ σ _ => by
    change w.ordered x σ ↔ v.ordered x σ
    cases v <;> cases w <;> first
      | exact absurd h (by decide)
      | exact Iff.rfl

/-- A set is the machine with a given number exactly if it is a singleton
whose element has that number. -/
theorem singleton_iff (x : Inst) (μ : ℕ) (h : μ < x.machines) (S : Finset (Fin x.machines)) :
    (S.card = 1 ∧ ∀ i ∈ S, i.val = μ) ↔ S = machineNumbered x μ := by
  have hm : machineNumbered x μ = {⟨μ, h⟩} := by
    ext i
    simp [machineNumbered, Fin.ext_iff]
  rw [hm]
  constructor
  · rintro ⟨hc, hall⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    exact congrArg _ (Fin.ext (hall a (Finset.mem_singleton_self a)))
  · rintro rfl
    simp

/-- The machine sets that encode stages admit the same sets of machines. -/
theorem stages_iff (x : Inst) (h0 : 0 < x.machines) {j : Fin x.jobs} (k : Fin (x.ops j))
    (S : Finset (Fin x.machines)) :
    (S.card = 1 ∧ ∀ i ∈ S, (k.val = 0 ∧ i.val = 0) ∨ (k.val ≠ 0 ∧ i.val ≠ 0)) ↔
      ((k.val = 0 → S = machineNumbered x 0) ∧
        (k.val ≠ 0 → S.card = 1 ∧ ∀ i ∈ S, i.val ≠ 0)) := by
  by_cases hk : k.val = 0
  · have := singleton_iff x 0 h0 S
    simpa [hk] using this
  · simp [hk]

/-- Reading the machines with a more general value keeps the data
admissible. -/
theorem machines_admits_mono (v w : Machines) (h : Machines.le v w = true) (x : Inst)
    (d : v.Data x) : v.admits d → w.admits (Machines.embed h x d) := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h Bool.false_ne_true
    | exact hv
    | exact trivial
    | exact ⟨hv, fun j k k' hk => Fin.ext hk⟩
    | exact hv.1

/-- Reading the machines with a more general value does not change the
admissible sets of machines. -/
theorem machines_view_iff (v w : Machines) (h : Machines.le v w = true) (x : Inst)
    (d : v.Data x) (hv : v.admits d) (j : Fin x.jobs) (k : Fin (x.ops j))
    (S : Finset (Fin x.machines)) :
    w.view (Machines.embed h x d) j k S ↔ v.view d j k S := by
  revert j k S
  cases v <;> cases w <;> first
    | exact absurd h Bool.false_ne_true
    | exact fun _ _ _ => Iff.rfl
    | exact fun j k S => singleton_iff x _ (hv j k) S
    | exact fun j k S => singleton_iff x _ (hv.1 j k) S
    | exact fun j k S => stages_iff x hv k S

/--
---
conclusion: Lax434175.Shops.machineSets_sound
---
An operation with a given machine has the machine set and the fixed set
consisting of that machine alone.
-/
theorem machineSets_sound : machineSets.Sound where
  admits := fun (v w : Machines) h x (d : v.Data x) hv => machines_admits_mono v w h x d hv
  constraint := fun (v w : Machines) h x (d : v.Data x) _ hv =>
    forall_congr' fun j => forall_congr' fun k => machines_view_iff v w h x d hv j k _

/-- A more special processing-time restriction has fewer instances. -/
theorem processingTimes_mono (v w : ProcessingTimes) (h : v.rank ≤ w.rank) (x : Inst) :
    v.holds x → w.holds x := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | exact hv
    | exact trivial
    | exact ⟨1, hv⟩

/--
---
conclusion: Lax434175.Shops.processingTimes_sound
---
-/
theorem processingTimes_sound : processingTimes.Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : ProcessingTimes) h x _ hv => by
    have h' : v.rank ≤ w.rank := of_decide_eq_true h
    have hv' : v.holds x := hv
    change w.holds x
    cases v <;> cases w <;> first
      | exact absurd h' (by decide)
      | exact hv'
      | exact trivial
      | exact ⟨1, hv'⟩

/--
---
conclusion: Lax434175.Shops.noWait_sound
---
-/
theorem noWait_sound : noWait.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : NoWait) h x _ σ _ => by
    have h' : v = w := of_decide_eq_true h
    subst h'
    exact Iff.rfl

end Lax434175Proofs.Shops
