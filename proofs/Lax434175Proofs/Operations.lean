import Mathlib.Tactic
import Lax434175.Operations
import Lax434175Proofs.MachineSets
import Lax434175Proofs.Shops
import Lax434175Proofs.ShopExtras
import Lax434175Proofs.Transportation
import Lax434175Proofs.Servers
import Lax434175Proofs.Preemptive

namespace Lax434175Proofs.Operations
open Lax434175.Kernels Lax434175.Modules Lax434175 Lax434175.Operations

/--
---
conclusion: Lax434175.Operations.interruption_sound
---
-/
theorem interruption_sound : Operations.interruption.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint v w h _ _ _ _ := by
    change Interruption.Mode at v w
    cases v <;> cases w <;> first | exact Iff.rfl | exact absurd h (by decide)

/--
---
conclusion: Lax434175.Operations.jobStructure_sound
---
With one operation per job there is no order to respect.
-/
theorem jobStructure_sound : Operations.jobStructure.Sound where
  admits := fun (v w : Structure) h x _ hv => by
    change w.holds x
    cases v <;> cases w <;> first
      | exact absurd h (by decide)
      | exact hv
      | exact trivial
  constraint := fun (v w : Structure) h x _ σ hv => by
    change w.ordered x σ ↔ v.ordered x σ
    cases v <;> cases w <;> first
      | exact absurd h (by decide)
      | exact Iff.rfl
      | skip
    have h1 : ∀ j, x.ops j = 1 := hv
    refine ⟨fun _ => trivial, fun _ j k k' hk => ?_⟩
    have := h1 j
    have hk1 := k.isLt
    have hk2 := k'.isLt
    have : k.val < k'.val := hk
    omega

/--
---
conclusion: Lax434175.Operations.environment_sound
---
Identical machines are uniform machines of speed one.
-/
theorem environment_sound : Operations.environment.Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : ParallelMachines.Environment) h x _ hv => by
    have h' : v.rank ≤ w.rank := of_decide_eq_true h
    have hv' : environmentHolds v x := hv
    change environmentHolds w x
    cases v <;> cases w <;> first
      | exact absurd h' (by decide)
      | exact hv'
      | exact trivial
      | skip
    refine ⟨fun o => if h : 0 < x.machines then x.p o.1 o.2 ⟨0, h⟩ else 0, fun _ => 1,
      fun o i => ?_⟩
    have hpos : 0 < x.machines := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    simp only [hpos, dite_true, Nat.mul_one, Nat.lt_one_iff, true_and]
    exact hv' o i _

/--
---
conclusion: Lax434175.Operations.processingTimes_sound
---
-/
theorem processingTimes_sound : Operations.processingTimes.Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : ParallelMachines.ProcessingTimes) h x _ hv => by
    have hv' : processingTimesHolds v x := hv
    change processingTimesHolds w x
    cases v <;> cases w <;> first
      | exact absurd h (by decide)
      | exact hv'
      | exact trivial
      | exact ⟨1, hv'⟩
      | exact fun o i => Or.inl (hv' o i)

theorem machines_admits_mono : ∀ (v w : Machines) (h : Machines.le v w = true) (x : Inst)
    (d : v.Data x), v.admits d → w.admits (Machines.embed h x d)
  | .par _, .par _, _, _, _, _ => trivial
  | .shop v, .shop w, h, x, d, hv => Shops.machines_admits_mono v w h x.toShop d hv
  | .par v, .shop w, h, _, _, _ => by
    cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | trivial
  | .shop _, .par _, h, _, _, _ => absurd h Bool.false_ne_true

theorem machines_view_iff : ∀ (v w : Machines) (h : Machines.le v w = true) (x : Inst)
    (d : v.Data x), v.admits d → ∀ o S, w.view (Machines.embed h x d) o S ↔ v.view d o S
  | .par v, .par w, h, x, d, _, o, S => by
    have h' : MachineSets.le v w = true := h
    change MachineSets.view w (MachineSets.embed h' x.toPar d) o.1 S ↔ MachineSets.view v d o.1 S
    rw [MachineSets.view_embed v w h' x.toPar d]
  | .shop v, .shop w, h, x, d, hv, o, S => Shops.machines_view_iff v w h x.toShop d hv o.1 o.2 S
  | .par v, .shop w, h, x, d, _, o, S => by
    cases v <;> cases w <;> first
      | exact absurd h Bool.false_ne_true
      | exact Iff.rfl
      | simp [Machines.view, Machines.embed, crossEmbed, Shops.Machines.view, MachineSets.view]
  | .shop _, .par _, h, _, _, _, _, _ => absurd h Bool.false_ne_true

/--
---
conclusion: Lax434175.Operations.machineSets_sound
---
A machine-set value of parallel machines restricts the operations of a job
alike, so it is read as a machine value of shops by repeating it for every
operation.
-/
theorem machineSets_sound : Operations.machineSets.Sound where
  admits := fun v w h x d hv => machines_admits_mono v w h x d hv
  constraint := fun v w h x d _ hv =>
    forall_congr' fun q => forall_congr' fun _ => machines_view_iff v w h x d hv q.op _

/--
---
conclusion: Lax434175.Operations.server_sound
---
-/
theorem server_sound : Operations.server.Sound where
  admits := fun (v w : Servers.Value) h _ d hv => Servers.admits_mono v w h d hv
  constraint := fun (v w : Servers.Value) h x d σ _ => by
    change (∀ s, Servers.view w (Servers.embed h d) = some s → _) ↔
      (∀ s, Servers.view v d = some s → _)
    rw [Servers.view_embed v w h d]

/--
---
conclusion: Lax434175.Operations.noWait_sound
---
-/
theorem noWait_sound : Operations.noWait.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : Shops.NoWait) h _ _ _ _ => by
    have h' : v = w := of_decide_eq_true h
    subst h'
    exact Iff.rfl

/--
---
conclusion: Lax434175.Operations.transportation_sound
---
-/
theorem transportation_sound : Operations.transportation.Sound where
  admits := fun (v w : Transportation.Value) h x (d : Transportation.Data x.toShop) hv =>
    Transportation.admits_mono h d hv
  constraint := fun (v w : Transportation.Value) h x (d : Transportation.Data x.toShop) σ _ => by
    have hr : v.robot = w.robot := (Transportation.le_parts h).2.1
    change (Delayed x d.1 σ ∧ (w.robot = true → Carried x d.1 d.2 σ)) ↔
      (Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ))
    rw [hr]

/--
---
conclusion: Lax434175.Operations.noIdle_sound
---
-/
theorem noIdle_sound : Operations.noIdle.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : ShopExtras.NoIdle) h _ _ _ _ => by
    have h' : v = w := of_decide_eq_true h
    subst h'
    exact Iff.rfl

/--
---
conclusion: Lax434175.Operations.batchSetups_sound
---
-/
theorem batchSetups_sound : Operations.batchSetups.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : ShopExtras.BatchSetups) h x d σ _ => by
    have hb := ShopExtras.batch_embed v w h x.toShop d
    have hs := ShopExtras.setup_embed v w h x.toShop d
    simp only [Operations.batchSetups, hb, hs]

/--
---
conclusion: Lax434175.Operations.startsBeforeCompletion
---
-/
theorem startsBeforeCompletion : Operations.kernel.StartsBeforeCompletion := by
  intro x σ _ j
  change (((piecesOfJob σ j).map Piece.start).min?).getD 0 ≤
    (((piecesOfJob σ j).map Piece.finish).max?).getD 0
  cases hL : piecesOfJob σ j with
  | nil => simp
  | cons q L =>
    have h1 := Preemptive.min_getD_le ((q :: L).map Piece.start) q.start (by simp)
    have h2 := Preemptive.le_max_getD ((q :: L).map Piece.finish) q.finish (by simp)
    have h3 : q.start ≤ q.finish := by unfold Piece.finish; exact le_self_add
    exact le_trans h1 (le_trans h3 h2)

end Lax434175Proofs.Operations
