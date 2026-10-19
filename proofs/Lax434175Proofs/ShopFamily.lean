import Lax434175.ShopFamily
import Lax434175Proofs.ShopProblems
import Lax434175Proofs.PreemptiveShopProblems
import Lax434175Proofs.Shops
import Lax434175Proofs.ShopExtras
import Lax434175Proofs.Transportation
import Lax434175Proofs.Servers
import Lax434175Proofs.ParallelFamily

namespace Lax434175Proofs.ShopFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Shops Lax434175.ShopFamily

section Soundness

theorem interruption_sound : ShopFamily.interruption.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint v w h _ _ _ _ := by
    change Interruption.Mode at v w
    cases v <;> cases w <;> first | exact Iff.rfl | exact absurd h (by decide)

theorem shopType_sound : ShopFamily.shopType.Sound where
  admits := fun (v w : ShopType) h x _ hv => Shops.shopType_holds_mono v w h x hv
  constraint := fun (v w : ShopType) h x _ σ _ => by
    change PreemptiveShops.ordered w x σ ↔ PreemptiveShops.ordered v x σ
    cases v <;> cases w <;> first
      | exact absurd h (by decide)
      | exact Iff.rfl

theorem machineSets_sound : ShopFamily.machineSets.Sound where
  admits := fun (v w : Machines) h x (d : v.Data x) hv => Shops.machines_admits_mono v w h x d hv
  constraint := fun (v w : Machines) h x (d : v.Data x) _ hv =>
    forall_congr' fun q => forall_congr' fun _ =>
      Shops.machines_view_iff v w h x d hv q.op.1 q.op.2 _

theorem processingTimes_sound : ShopFamily.processingTimes.Sound where
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

theorem noWait_sound : ShopFamily.noWait.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : NoWait) h _ _ _ _ => by
    have h' : v = w := of_decide_eq_true h
    subst h'
    exact Iff.rfl

theorem transportation_sound : ShopFamily.transportation.Sound where
  admits := fun (v w : Transportation.Value) h x (d : Transportation.Data x) hv =>
    Transportation.admits_mono h d hv
  constraint := fun (v w : Transportation.Value) h x (d : Transportation.Data x) σ _ => by
    have hr : v.robot = w.robot := (Transportation.le_parts h).2.1
    change (Delayed x d.1 σ ∧ (w.robot = true → Carried x d.1 d.2 σ)) ↔
      (Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ))
    rw [hr]

theorem server_sound : ShopFamily.server.Sound where
  admits := fun (v w : Servers.Value) h _ d hv => Servers.admits_mono v w h d hv
  constraint := fun (v w : Servers.Value) h x d σ _ => by
    change (∀ s, Servers.view w (Servers.embed h d) = some s → _) ↔
      (∀ s, Servers.view v d = some s → _)
    rw [Servers.view_embed v w h d]

theorem noIdle_sound : ShopFamily.noIdle.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : ShopExtras.NoIdle) h _ _ _ _ => by
    have h' : v = w := of_decide_eq_true h
    subst h'
    exact Iff.rfl

theorem batchSetups_sound : ShopFamily.batchSetups.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : ShopExtras.BatchSetups) h (x : Inst) (d : v.Data x) σ _ => by
    have hb := ShopExtras.batch_embed v w h x d
    have hs := ShopExtras.setup_embed v w h x d
    simp only [ShopFamily.batchSetups, hb, hs]

/--
---
conclusion: Lax434175.ShopFamily.family_sound
---
-/
theorem family_sound : ShopFamily.family.Sound where
  module
    | .interruption => interruption_sound
    | .field .shopType => shopType_sound
    | .field .machineSets => machineSets_sound
    | .field .machineCount => Counts.sound _ _
    | .field .jobCount => Counts.sound _ _
    | .field .processingTimes => processingTimes_sound
    | .field .noWait => noWait_sound
    | .field .transportation => transportation_sound
    | .field .server => server_sound
    | .field .noIdle => noIdle_sound
    | .field .batchSetups => batchSetups_sound
    | .field .releaseDates => ReleaseDates.sound _
    | .field .deadlines => Deadlines.sound _
    | .field .precedence => Precedence.sound _ _
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.ShopFamily.specialCase_of_le
---
-/
theorem specialCase_of_le {s t : Spec ShopFamily.family} :
    s.le t → SpecialCase (problem ShopFamily.family s) (problem ShopFamily.family t) :=
  fun h => ⟨lift ShopFamily.family family_sound h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.ShopFamily.reducible_of_reduces
---
-/
theorem reducible_of_reduces {s t : Spec ShopFamily.family} :
    Thresholds.Reduces s t →
      Reducible (problem ShopFamily.family s) (problem ShopFamily.family t) :=
  Thresholds.reducible_of_reduces family_sound.module

end Soundness

section Kernels

/-- The schedules of a machine model on shop instances. -/
structure SSys where
  Sched : Inst → Type
  feasible : (x : Inst) → Sched x → Prop
  start : (x : Inst) → Sched x → Fin x.jobs → NNRat
  completion : (x : Inst) → Sched x → Fin x.jobs → NNRat

/-- The kernel with these schedules. -/
abbrev SSys.kernel (P : SSys) : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := P.Sched
  feasible := P.feasible
  start := P.start
  completion := P.completion

/-- Non-preemptive shop schedules. -/
abbrev shopSys : SSys where
  Sched := Shops.Sched
  feasible := Shops.feasible
  start x σ j := (jobStart x σ j : NNRat)
  completion x σ j := (jobCompletion x σ j : NNRat)

/-- Preemptive shop schedules. -/
abbrev pshopSys : SSys where
  Sched := PreemptiveShops.Sched
  feasible := PreemptiveShops.feasible
  start _ σ j := (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.start).min?).getD 0
  completion _ σ j :=
    (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.finish).max?).getD 0

/-- Shop schedules with pieces. -/
abbrev newSys : SSys where
  Sched := PreemptiveShops.Sched
  feasible _ σ := ShopFamily.feasible σ
  start _ σ j := (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.start).min?).getD 0
  completion _ σ j :=
    (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.finish).max?).getD 0

example : Shops.kernel = shopSys.kernel := rfl
example : PreemptiveShops.kernel = pshopSys.kernel := rfl
example : ShopFamily.kernel = newSys.kernel := rfl

variable {P Q : SSys} {x : Inst} {σ : P.Sched x} {τ : Q.Sched x}

theorem release_admits (v d) :
    (ReleaseDates.module P.kernel).admits v x d → (ReleaseDates.module Q.kernel).admits v x d := by
  intro h
  cases v <;> exact h

/-- Deadlines of an instance read in another machine model. -/
def deadlinesData (P Q : SSys) (v : Deadlines.Value)
    (d : (Deadlines.module P.kernel).Data v x) : (Deadlines.module Q.kernel).Data v x := by
  cases v <;> exact d

/-- Objective data of an instance read in another machine model. -/
def objectiveData (P Q : SSys) (v : Objectives.Value)
    (d : Objectives.Data P.kernel v x) : Objectives.Data Q.kernel v x := by
  cases v <;> exact d

theorem objective_admits (v d) :
    Objectives.admits (K := P.kernel) v x d →
      Objectives.admits (K := Q.kernel) v x (objectiveData P Q v d) := by
  intro ha
  cases v <;> exact ha

theorem cost_eq (h : ∀ j, Q.completion x τ j = P.completion x σ j) (v d) :
    Objectives.cost (K := Q.kernel) v x (objectiveData P Q v d) τ =
      Objectives.cost (K := P.kernel) v x d σ := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, h] <;> rfl

theorem release_iff (h : ∀ j, Q.start x τ j = P.start x σ j) (v d) :
    (ReleaseDates.module Q.kernel).constraint v x d τ ↔
      (ReleaseDates.module P.kernel).constraint v x d σ := by
  change (∀ j, (x.r j : NNRat) ≤ Q.start x τ j) ↔ ∀ j, (x.r j : NNRat) ≤ P.start x σ j
  simp only [h]

theorem deadlines_iff (h : ∀ j, Q.completion x τ j = P.completion x σ j) (v d) :
    (Deadlines.module Q.kernel).constraint v x (deadlinesData P Q v d) τ ↔
      (Deadlines.module P.kernel).constraint v x d σ := by
  cases v <;>
  · change (∀ j, Deadlines.Within (Q.completion x τ j) _) ↔
      ∀ j, Deadlines.Within (P.completion x σ j) _
    simp only [h]
    rfl

theorem precedence_iff (hs : ∀ j, Q.start x τ j = P.start x σ j)
    (hc : ∀ j, Q.completion x τ j = P.completion x σ j) (m : Inst → ℕ) (v d) :
    (Precedence.module Q.kernel m).constraint v x d τ ↔
      (Precedence.module P.kernel m).constraint v x d σ := by
  change (∀ i j, _ → (Q.completion x τ i : ℚ) + _ ≤ (Q.start x τ j : ℚ)) ↔
    ∀ i j, _ → (P.completion x σ i : ℚ) + _ ≤ (P.start x σ j : ℚ)
  simp only [hs, hc]

end Kernels

section Lists

open PreemptiveShops (Piece piecesOf piecesOfJob opStart opFinish)

theorem minCast (A : List NNRat) (B : List ℕ) (h : ∀ a, a ∈ A ↔ ∃ b ∈ B, a = (b : NNRat)) :
    (A.min?).getD 0 = ((B.min?.getD 0 : ℕ) : NNRat) := by
  cases hB : B.min? with
  | none =>
    have hA : A = [] := List.eq_nil_iff_forall_not_mem.mpr fun a ha => by
      obtain ⟨b, hb, -⟩ := (h a).mp ha
      simp [List.min?_eq_none_iff.mp hB] at hb
    simp [hA]
  | some m =>
    obtain ⟨hm, hall⟩ := List.min?_eq_some_iff.mp hB
    refine ParallelFamily.getD_min_eq A (m : NNRat) ((h _).mpr ⟨m, hm, rfl⟩) fun a ha => ?_
    obtain ⟨b, hb, rfl⟩ := (h a).mp ha
    exact_mod_cast hall b hb

theorem maxCast (A : List NNRat) (B : List ℕ) (h : ∀ a, a ∈ A ↔ ∃ b ∈ B, a = (b : NNRat)) :
    (A.max?).getD 0 = ((B.max?.getD 0 : ℕ) : NNRat) := by
  cases hB : B.max? with
  | none =>
    have hA : A = [] := List.eq_nil_iff_forall_not_mem.mpr fun a ha => by
      obtain ⟨b, hb, -⟩ := (h a).mp ha
      simp [List.max?_eq_none_iff.mp hB] at hb
    simp [hA]
  | some m =>
    obtain ⟨hm, hall⟩ := List.max?_eq_some_iff.mp hB
    refine ParallelFamily.getD_max_eq A (m : NNRat) ((h _).mpr ⟨m, hm, rfl⟩) fun a ha => ?_
    obtain ⟨b, hb, rfl⟩ := (h a).mp ha
    exact_mod_cast hall b hb

theorem mem_piecesOf {x : Inst} {σ : PreemptiveShops.Sched x} {o : Op x} {q : Piece x} :
    q ∈ piecesOf σ o ↔ q ∈ σ.pieces ∧ q.op = o := by
  unfold piecesOf
  simp

theorem mem_piecesOfJob {x : Inst} {σ : PreemptiveShops.Sched x} {j : Fin x.jobs} {q : Piece x} :
    q ∈ piecesOfJob σ j ↔ q ∈ σ.pieces ∧ q.op.1 = j := by
  unfold piecesOfJob
  simp

/-- A machine belongs to the machines of an operation if a piece of the
operation occupies it. -/
theorem mem_opMachines {x : Inst} {σ : PreemptiveShops.Sched x} {o : Op x} {i : Fin x.machines} :
    i ∈ opMachines σ o ↔ Occupies σ o i := by
  unfold opMachines Occupies
  rw [Transportation.mem_foldr_union]
  simp

theorem opStart_single {x : Inst} {σ : PreemptiveShops.Sched x} {o : Op x} {q : Piece x}
    (h : piecesOf σ o = [q]) : opStart σ o = q.start := by
  unfold opStart
  rw [h]
  rfl

theorem opFinish_single {x : Inst} {σ : PreemptiveShops.Sched x} {o : Op x} {q : Piece x}
    (h : piecesOf σ o = [q]) : opFinish σ o = q.finish := by
  unfold opFinish
  rw [h]
  rfl

/-- Two different pieces of a feasible schedule that belong to the same job or
share a machine do not overlap. -/
theorem apart_of_feasible {x : Inst} {σ : PreemptiveShops.Sched x}
    (hp : σ.pieces.Pairwise
      (fun a b => (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) →
        PreemptiveShops.Apart a b))
    {a b : Piece x} (ha : a ∈ σ.pieces) (hb : b ∈ σ.pieces) (hab : a ≠ b)
    (h : a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) : PreemptiveShops.Apart a b := by
  rcases ParallelFamily.pairwise_either hp ha hb hab with h' | h'
  · exact h' h
  · have h'' : b.op.1 = a.op.1 ∨ ¬ Disjoint b.machines a.machines := by
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr fun hd => h hd.symm
    rcases h' h'' with h3 | h3
    · exact Or.inr h3
    · exact Or.inl h3

end Lists

section Match

open PreemptiveShops (Piece piecesOf piecesOfJob opStart opFinish)

/-- A non-preemptive shop schedule and a schedule with pieces agree on every
operation and every job. -/
structure Match (x : Inst) (σ : Shops.Sched x) (τ : PreemptiveShops.Sched x) : Prop where
  opStart : ∀ o : Op x, opStart τ o = (σ.start o.1 o.2 : NNRat)
  opFinish : ∀ o : Op x, opFinish τ o = (finish x σ o : NNRat)
  uses : ∀ (o : Op x) S, (∃ q ∈ piecesOf τ o, q.machines = S) ↔ σ.machines o.1 o.2 = S
  start : ∀ j, newSys.start x τ j = shopSys.start x σ j
  completion : ∀ j, newSys.completion x τ j = shopSys.completion x σ j

variable {x : Inst} {σ : Shops.Sched x} {τ : PreemptiveShops.Sched x}

theorem machines_of_mem (h : Match x σ τ) {o : Op x} {q : Piece x} (hq : q ∈ piecesOf τ o) :
    q.machines = σ.machines o.1 o.2 :=
  ((h.uses o q.machines).mp ⟨q, hq, rfl⟩).symm

theorem shares_iff (h : Match x σ τ) (a b : Op x) :
    Shares τ a b ↔ ¬ Disjoint (σ.machines a.1 a.2) (σ.machines b.1 b.2) := by
  constructor
  · rintro ⟨qa, hqa, qb, hqb, hd⟩
    rwa [machines_of_mem h hqa, machines_of_mem h hqb] at hd
  · intro hd
    obtain ⟨qa, hqa, ha⟩ := (h.uses a _).mpr rfl
    obtain ⟨qb, hqb, hb⟩ := (h.uses b _).mpr rfl
    exact ⟨qa, hqa, qb, hqb, by rwa [ha, hb]⟩

theorem occupies_iff (h : Match x σ τ) (o : Op x) (i : Fin x.machines) :
    Occupies τ o i ↔ i ∈ σ.machines o.1 o.2 := by
  constructor
  · rintro ⟨q, hq, hi⟩
    rwa [machines_of_mem h hq] at hi
  · intro hi
    obtain ⟨q, hq, hS⟩ := (h.uses o _).mpr rfl
    exact ⟨q, hq, hS ▸ hi⟩

theorem opMachines_eq (h : Match x σ τ) (o : Op x) : opMachines τ o = σ.machines o.1 o.2 := by
  ext i
  rw [mem_opMachines, occupies_iff h]

theorem shopType_iff (h : Match x σ τ) (v : ShopType) :
    PreemptiveShops.ordered v x τ ↔ v.ordered x σ := by
  cases v
  · exact Iff.rfl
  all_goals
    simp only [PreemptiveShops.ordered, ShopType.ordered, PreemptiveShops.InOrder, InOrder,
      h.opStart, h.opFinish, Nat.cast_le]

theorem machineSets_iff (h : Match x σ τ) (v : Machines) (d : v.Data x) :
    (∀ q ∈ τ.pieces, v.view d q.op.1 q.op.2 q.machines) ↔
      ∀ j k, v.view d j k (σ.machines j k) := by
  constructor
  · intro H j k
    obtain ⟨q, hq, hS⟩ := (h.uses ⟨j, k⟩ _).mpr rfl
    obtain ⟨hq1, hq2⟩ := mem_piecesOf.mp hq
    have := H q hq1
    rcases q with ⟨o, M, st, len⟩
    simp only at hq2 hS this
    subst hq2 hS
    exact this
  · intro H q hq
    rw [machines_of_mem h (mem_piecesOf.mpr ⟨hq, rfl⟩)]
    exact H _ _

theorem noWait_iff (h : Match x σ τ) (v : NoWait) :
    (v = .noWait → ∀ j, newSys.completion x τ j =
      newSys.start x τ j + ∑ k, (x.p j k : NNRat)) ↔ v.constraint x σ := by
  cases v
  · simp [NoWait.constraint]
  · constructor
    · intro H j
      have := H rfl j
      rw [h.start j, h.completion j] at this
      change ((jobCompletion x σ j : ℕ) : NNRat) =
        ((jobStart x σ j : ℕ) : NNRat) + ∑ k, (x.p j k : NNRat) at this
      change jobCompletion x σ j = jobStart x σ j + ∑ k, x.p j k
      exact_mod_cast this
    · intro H _ j
      rw [h.start j, h.completion j]
      have H' : jobCompletion x σ j = jobStart x σ j + ∑ k, x.p j k := H j
      change ((jobCompletion x σ j : ℕ) : NNRat) =
        ((jobStart x σ j : ℕ) : NNRat) + ∑ k, (x.p j k : NNRat)
      exact_mod_cast H'

theorem delayed_iff (h : Match x σ τ) (hf : Shops.feasible x σ) (t : Transportation.Delays x) :
    Delayed x t τ ↔ Transportation.Delayed x t σ := by
  unfold Delayed Transportation.Delayed
  refine forall_congr' fun j => forall_congr' fun k => forall_congr' fun l =>
    forall_congr' fun hkl => ?_
  simp only [h.opStart, h.opFinish, ← Nat.cast_add, Nat.cast_le]
  constructor
  · rintro (⟨h1, h2⟩ | h3)
    · have hne : (⟨j, k⟩ : Op x) ≠ ⟨j, l⟩ := fun e => hkl (eq_of_heq (Sigma.mk.inj e).2)
      rw [h1, h2]
      simpa using hf.2 ⟨j, k⟩ ⟨j, l⟩ hne (Or.inl rfl)
    · exact h3
  · exact Or.inr

theorem carried_iff (h : Match x σ τ) (t : Transportation.Delays x)
    (e : Transportation.EmptyMoves x) :
    Carried x t e τ ↔ Transportation.Carried x t e σ := by
  unfold Carried Transportation.Carried
  simp only [h.opStart, h.opFinish, Nat.cast_le, opMachines_eq h]

theorem transportation_iff (h : Match x σ τ) (hf : Shops.feasible x σ)
    (v : Transportation.Value) (d : Transportation.Data x) :
    (Delayed x d.1 τ ∧ (v.robot = true → Carried x d.1 d.2 τ)) ↔
      (Transportation.Delayed x d.1 σ ∧
        (v.robot = true → Transportation.Carried x d.1 d.2 σ)) := by
  rw [delayed_iff h hf, carried_iff h]

theorem server_iff (h : Match x σ τ) (v : Servers.Value) (d : Servers.Data (Op x) v) :
    ShopFamily.server.constraint v x d τ ↔ Servers.shop.constraint v x d σ := by
  have e1 : (fun o : Op x => (opStart τ o : ℚ)) = fun o => (σ.start o.1 o.2 : ℚ) :=
    funext fun o => by rw [h.opStart]; simp
  have e2 : (fun o : Op x => (opFinish τ o : ℚ)) = fun o => (finish x σ o : ℚ) :=
    funext fun o => by rw [h.opFinish]; simp
  have e3 : Shares τ = fun a b => ¬ Disjoint (σ.machines a.1 a.2) (σ.machines b.1 b.2) :=
    funext fun a => funext fun b => propext (shares_iff h a b)
  have e4 : (fun o : Op x => (kernel.start x τ o.1 : ℚ)) =
      fun o => (Shops.jobStart x σ o.1 : ℚ) :=
    funext fun o => by
      have := h.start o.1
      change kernel.start x τ o.1 = ((Shops.jobStart x σ o.1 : ℕ) : NNRat) at this
      rw [this]; simp
  change (∀ s, Servers.view v d = some s → Servers.Served (fun o : Op x => (opStart τ o : ℚ))
      (fun o => (opFinish τ o : ℚ))
      (Servers.setupRelease (fun o : Op x => (opStart τ o : ℚ))
        (fun o => (kernel.start x τ o.1 : ℚ)) (fun o => (x.r o.1 : ℚ)))
      (Shares τ) s) ↔ _
  rw [e1, e2, e3, e4]
  rfl

theorem noIdle_iff (h : Match x σ τ) (v : ShopExtras.NoIdle) :
    (v = .noIdle → Contiguous x τ) ↔ (v = .noIdle → ShopExtras.Contiguous x σ) := by
  unfold Contiguous ShopExtras.Contiguous ShopExtras.Occupies
  simp only [occupies_iff h, h.opStart, h.opFinish, Nat.cast_inj, Nat.cast_le]

theorem batchSetups_iff (h : Match x σ τ) (v : ShopExtras.BatchSetups) (d : v.Data x) :
    ShopFamily.batchSetups.constraint v x d τ ↔ ShopExtras.batchSetups.constraint v x d σ := by
  dsimp only [ShopFamily.batchSetups, ShopExtras.batchSetups, Follows, ShopExtras.Follows]
  unfold ShopExtras.Occupies
  simp only [shares_iff h, occupies_iff h, h.opStart, h.opFinish, ← Nat.cast_add, Nat.cast_le]

end Match

section Translate

open PreemptiveShops (Piece piecesOf piecesOfJob opStart opFinish)

variable {x : Inst}

/-- The piece of an operation in a non-preemptive shop schedule. -/
def piece (σ : Shops.Sched x) (o : Op x) : Piece x :=
  ⟨o, σ.machines o.1 o.2, (σ.start o.1 o.2 : NNRat), (x.p o.1 o.2 : NNRat)⟩

/-- A non-preemptive shop schedule as a schedule with pieces. -/
noncomputable def toPieces (x : Inst) (σ : Shops.Sched x) : PreemptiveShops.Sched x :=
  ⟨(Finset.univ : Finset (Op x)).toList.map (piece σ)⟩

theorem piecesOf_toPieces (σ : Shops.Sched x) (o : Op x) :
    piecesOf (toPieces x σ) o = [piece σ o] := by
  unfold piecesOf toPieces
  rw [List.filter_map]
  have e : ((fun q : Piece x => decide (q.op = o)) ∘ piece σ) = fun o' => decide (o' = o) := rfl
  rw [e, List.filter_eq, List.count_eq_one_of_mem (Finset.nodup_toList _)
    (Finset.mem_toList.mpr (Finset.mem_univ o))]
  rfl

theorem finish_piece (σ : Shops.Sched x) (o : Op x) :
    (piece σ o).finish = (finish x σ o : NNRat) := by
  simp [PreemptiveShops.Piece.finish, piece, finish]

theorem toPieces_match (σ : Shops.Sched x) : Match x σ (toPieces x σ) := by
  have hjob : ∀ j q, q ∈ piecesOfJob (toPieces x σ) j ↔ ∃ k, q = piece σ ⟨j, k⟩ := by
    intro j q
    rw [mem_piecesOfJob]
    unfold toPieces
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨o, rfl⟩, hj⟩
      obtain ⟨j', k⟩ := o
      simp only [piece] at hj
      subst hj
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨⟨⟨j, k⟩, rfl⟩, rfl⟩
  refine ⟨fun o => ?_, fun o => ?_, fun o S => ?_, fun j => ?_, fun j => ?_⟩
  · rw [opStart_single (piecesOf_toPieces σ o)]
    rfl
  · rw [opFinish_single (piecesOf_toPieces σ o), finish_piece]
  · rw [piecesOf_toPieces]
    simp [piece]
  · refine minCast _ _ fun a => ?_
    simp only [List.mem_map, hjob, List.mem_ofFn]
    constructor
    · rintro ⟨q, ⟨k, rfl⟩, rfl⟩
      exact ⟨σ.start j k, ⟨k, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨k, rfl⟩, rfl⟩
      exact ⟨piece σ ⟨j, k⟩, ⟨k, rfl⟩, rfl⟩
  · refine maxCast _ _ fun a => ?_
    simp only [List.mem_map, hjob, List.mem_ofFn]
    constructor
    · rintro ⟨q, ⟨k, rfl⟩, rfl⟩
      exact ⟨finish x σ ⟨j, k⟩, ⟨k, rfl⟩, (finish_piece σ ⟨j, k⟩)⟩
    · rintro ⟨b, ⟨k, rfl⟩, rfl⟩
      exact ⟨piece σ ⟨j, k⟩, ⟨k, rfl⟩, finish_piece σ ⟨j, k⟩⟩

theorem toPieces_feasible (σ : Shops.Sched x) (hf : Shops.feasible x σ) :
    ShopFamily.feasible (toPieces x σ) ∧ ShopFamily.holds .none x (toPieces x σ) := by
  refine ⟨⟨fun q hq => ?_, ?_⟩, fun o => ⟨piece σ o, piecesOf_toPieces σ o, rfl, σ.start o.1 o.2, rfl⟩⟩
  · obtain ⟨o, -, rfl⟩ := List.mem_map.mp hq
    exact hf.1 o
  · unfold toPieces
    refine List.Pairwise.map _ (fun a b h => h) ?_
    refine (Finset.nodup_toList _).pairwise_of_forall_ne fun a _ b _ hab hc => ?_
    unfold PreemptiveShops.Apart
    rw [finish_piece, finish_piece]
    rcases hf.2 a b hab hc with h | h
    · exact Or.inl (show _ ≤ ((σ.start b.1 b.2 : ℕ) : NNRat) by exact_mod_cast h)
    · exact Or.inr (show _ ≤ ((σ.start a.1 a.2 : ℕ) : NNRat) by exact_mod_cast h)

/-- A shop schedule with pieces read as a non-preemptive one: every operation
is processed by its first piece. -/
noncomputable def ofPieces (x : Inst) (τ : PreemptiveShops.Sched x) : Shops.Sched x where
  machines j k := (((piecesOf τ ⟨j, k⟩).head?).map Piece.machines).getD ∅
  start j k := Classical.epsilon fun n : ℕ =>
    ((piecesOf τ ⟨j, k⟩).head?).map Piece.start = some (n : NNRat)

theorem ofPieces_single {τ : PreemptiveShops.Sched x} {o : Op x} {q : Piece x}
    (h : piecesOf τ o = [q]) (n : ℕ) (hn : q.start = (n : NNRat)) :
    (ofPieces x τ).machines o.1 o.2 = q.machines ∧
      ((ofPieces x τ).start o.1 o.2 : NNRat) = q.start := by
  refine ⟨by simp [ofPieces, h], ?_⟩
  have hs : ((piecesOf τ o).head?).map Piece.start = some ((Classical.epsilon fun n : ℕ =>
      ((piecesOf τ o).head?).map Piece.start = some (n : NNRat) : ℕ) : NNRat) :=
    Classical.epsilon_spec (p := fun n : ℕ =>
      ((piecesOf τ o).head?).map Piece.start = some (n : NNRat)) ⟨n, by simp [h, hn]⟩
  change ((Classical.epsilon fun n : ℕ =>
      ((piecesOf τ o).head?).map Piece.start = some (n : NNRat) : ℕ) : NNRat) = q.start
  generalize (Classical.epsilon fun n : ℕ =>
      ((piecesOf τ o).head?).map Piece.start = some (n : NNRat)) = e at hs ⊢
  rw [h] at hs
  exact (Option.some.inj hs).symm

theorem ofPieces_back (τ : PreemptiveShops.Sched x) (hf : ShopFamily.feasible τ)
    (hm : ShopFamily.holds .none x τ) :
    Shops.feasible x (ofPieces x τ) ∧ Match x (ofPieces x τ) τ := by
  have key : ∀ o : Op x, ∃ q, piecesOf τ o = [q] ∧ (ofPieces x τ).machines o.1 o.2 = q.machines ∧
      ((ofPieces x τ).start o.1 o.2 : NNRat) = q.start ∧
      (finish x (ofPieces x τ) o : NNRat) = q.finish := by
    intro o
    obtain ⟨q, hq, hl, n, hn⟩ := hm o
    obtain ⟨h1, h2⟩ := ofPieces_single hq n hn
    refine ⟨q, hq, h1, h2, ?_⟩
    unfold finish
    push_cast
    rw [h2, PreemptiveShops.Piece.finish, hl]
  have mem : ∀ o q, piecesOf τ o = [q] → q ∈ τ.pieces ∧ q.op = o := fun o q h =>
    mem_piecesOf.mp (h ▸ List.mem_singleton_self q)
  -- the pieces of a job are the pieces of its operations
  have hjob : ∀ (j : Fin x.jobs) (q : Piece x), q ∈ piecesOfJob τ j ↔
      ∃ k, piecesOf τ ⟨j, k⟩ = [q] := by
    intro j q
    rw [mem_piecesOfJob]
    constructor
    · rintro ⟨hq, hj⟩
      obtain ⟨q', hq', -⟩ := key q.op
      have hqq : q ∈ piecesOf τ q.op := mem_piecesOf.mpr ⟨hq, rfl⟩
      rw [hq', List.mem_singleton] at hqq
      subst hqq
      rcases q with ⟨⟨j', k⟩, M, st, len⟩
      simp only at hj hq'
      subst hj
      exact ⟨k, hq'⟩
    · rintro ⟨k, hk⟩
      obtain ⟨h1, h2⟩ := mem _ _ hk
      exact ⟨h1, by rw [h2]⟩
  refine ⟨⟨fun o => ?_, fun a b hab hc => ?_⟩, fun o => ?_, fun o => ?_, fun o S => ?_,
    fun j => ?_, fun j => ?_⟩
  · obtain ⟨q, hq, h1, -⟩ := key o
    rw [h1]
    exact hf.1 q (mem o q hq).1
  · obtain ⟨qa, hqa, ha1, ha2, ha3⟩ := key a
    obtain ⟨qb, hqb, hb1, hb2, hb3⟩ := key b
    have hma := mem a qa hqa
    have hmb := mem b qb hqb
    have hne : qa ≠ qb := fun e => hab (hma.2.symm.trans (e ▸ hmb.2))
    have hc' : qa.op.1 = qb.op.1 ∨ ¬ Disjoint qa.machines qb.machines := by
      rw [hma.2, hmb.2, ← ha1, ← hb1]
      exact hc
    rcases apart_of_feasible hf.2 hma.1 hmb.1 hne hc' with h | h
    · left
      have : (finish x (ofPieces x τ) a : NNRat) ≤ ((ofPieces x τ).start b.1 b.2 : NNRat) := by
        rw [ha3, hb2]
        exact h
      exact_mod_cast this
    · right
      have : (finish x (ofPieces x τ) b : NNRat) ≤ ((ofPieces x τ).start a.1 a.2 : NNRat) := by
        rw [hb3, ha2]
        exact h
      exact_mod_cast this
  · obtain ⟨q, hq, -, h2, -⟩ := key o
    rw [opStart_single hq, h2]
  · obtain ⟨q, hq, -, -, h3⟩ := key o
    rw [opFinish_single hq, h3]
  · obtain ⟨q, hq, h1, -⟩ := key o
    rw [hq, h1]
    simp
  · refine minCast _ _ fun a => ?_
    simp only [List.mem_map, hjob, List.mem_ofFn]
    constructor
    · rintro ⟨q, ⟨k, hk⟩, rfl⟩
      obtain ⟨q', hq', -, h2, -⟩ := key ⟨j, k⟩
      rw [hk, List.cons.injEq] at hq'
      exact ⟨(ofPieces x τ).start j k, ⟨k, rfl⟩, by rw [h2, hq'.1]⟩
    · rintro ⟨b, ⟨k, rfl⟩, rfl⟩
      obtain ⟨q, hq, -, h2, -⟩ := key ⟨j, k⟩
      exact ⟨q, ⟨k, hq⟩, h2.symm⟩
  · refine maxCast _ _ fun a => ?_
    simp only [List.mem_map, hjob, List.mem_ofFn]
    constructor
    · rintro ⟨q, ⟨k, hk⟩, rfl⟩
      obtain ⟨q', hq', -, -, h3⟩ := key ⟨j, k⟩
      rw [hk, List.cons.injEq] at hq'
      exact ⟨finish x (ofPieces x τ) ⟨j, k⟩, ⟨k, rfl⟩, by rw [h3, hq'.1]⟩
    · rintro ⟨b, ⟨k, rfl⟩, rfl⟩
      obtain ⟨q, hq, -, -, h3⟩ := key ⟨j, k⟩
      exact ⟨q, ⟨k, hq⟩, h3.symm⟩

end Translate

section ShopFaithful

/-- A non-preemptive shop instance read in the family. -/
def toNewS {s : Spec ShopProblems.family} (x : Assembly.Inst ShopProblems.family s) :
    Assembly.Inst ShopFamily.family (ofShop s) where
  base := x.base
  data
    | .interruption => ()
    | .field .shopType => x.data .shopType
    | .field .machineSets => x.data .machineSets
    | .field .machineCount => x.data .machineCount
    | .field .jobCount => x.data .jobCount
    | .field .processingTimes => x.data .processingTimes
    | .field .noWait => x.data .noWait
    | .field .transportation => x.data .transportation
    | .field .server => x.data .server
    | .field .noIdle => x.data .noIdle
    | .field .batchSetups => x.data .batchSetups
    | .field .releaseDates => x.data .releaseDates
    | .field .deadlines => deadlinesData shopSys newSys _ (x.data .deadlines)
    | .field .precedence => x.data .precedence
  admitted
    | .interruption => trivial
    | .field .shopType => x.admitted .shopType
    | .field .machineSets => x.admitted .machineSets
    | .field .machineCount => x.admitted .machineCount
    | .field .jobCount => x.admitted .jobCount
    | .field .processingTimes => x.admitted .processingTimes
    | .field .noWait => x.admitted .noWait
    | .field .transportation => x.admitted .transportation
    | .field .server => x.admitted .server
    | .field .noIdle => x.admitted .noIdle
    | .field .batchSetups => x.admitted .batchSetups
    | .field .releaseDates =>
      release_admits (P := shopSys) (Q := newSys) (s.module .releaseDates) ()
        (x.admitted .releaseDates)
    | .field .deadlines => trivial
    | .field .precedence => x.admitted .precedence
  objectiveData := objectiveData shopSys newSys _ x.objectiveData
  objectiveAdmitted :=
    objective_admits (P := shopSys) (Q := newSys) s.objective x.objectiveData x.objectiveAdmitted

/-- An instance of the family without interruption read as a non-preemptive
shop instance. -/
def toOldS {s : Spec ShopProblems.family} (y : Assembly.Inst ShopFamily.family (ofShop s)) :
    Assembly.Inst ShopProblems.family s where
  base := y.base
  data
    | .shopType => y.data (.field .shopType)
    | .machineSets => y.data (.field .machineSets)
    | .machineCount => y.data (.field .machineCount)
    | .jobCount => y.data (.field .jobCount)
    | .processingTimes => y.data (.field .processingTimes)
    | .noWait => y.data (.field .noWait)
    | .transportation => y.data (.field .transportation)
    | .server => y.data (.field .server)
    | .noIdle => y.data (.field .noIdle)
    | .batchSetups => y.data (.field .batchSetups)
    | .releaseDates => y.data (.field .releaseDates)
    | .deadlines => deadlinesData newSys shopSys _ (y.data (.field .deadlines))
    | .precedence => y.data (.field .precedence)
  admitted
    | .shopType => y.admitted (.field .shopType)
    | .machineSets => y.admitted (.field .machineSets)
    | .machineCount => y.admitted (.field .machineCount)
    | .jobCount => y.admitted (.field .jobCount)
    | .processingTimes => y.admitted (.field .processingTimes)
    | .noWait => y.admitted (.field .noWait)
    | .transportation => y.admitted (.field .transportation)
    | .server => y.admitted (.field .server)
    | .noIdle => y.admitted (.field .noIdle)
    | .batchSetups => y.admitted (.field .batchSetups)
    | .releaseDates =>
      release_admits (P := newSys) (Q := shopSys) (s.module .releaseDates) ()
        (y.admitted (.field .releaseDates))
    | .deadlines => trivial
    | .precedence => y.admitted (.field .precedence)
  objectiveData := objectiveData newSys shopSys _ y.objectiveData
  objectiveAdmitted :=
    objective_admits (P := newSys) (Q := shopSys) s.objective y.objectiveData y.objectiveAdmitted

variable {s : Spec ShopProblems.family}

theorem fields_toNewS (x : Assembly.Inst ShopProblems.family s) {σ : Shops.Sched x.base}
    {τ : PreemptiveShops.Sched x.base} (h : Match x.base σ τ) (hf : Shops.feasible x.base σ)
    (i : ShopProblems.FieldName) :
    (ShopProblems.family.module i).constraint (s.module i) x.base (x.data i) σ ↔
      (ShopFamily.family.module (.field i)).constraint ((ofShop s).module (.field i)) x.base
        ((toNewS x).data (.field i)) τ := by
  cases i
  · exact (shopType_iff h _).symm
  · exact (machineSets_iff h _ _).symm
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact (noWait_iff h _).symm
  · exact (transportation_iff h hf _ _).symm
  · exact (server_iff h _ _).symm
  · exact (noIdle_iff h _).symm
  · exact (batchSetups_iff h _ _).symm
  · exact (release_iff (P := shopSys) (Q := newSys) h.start _ _).symm
  · exact (deadlines_iff (P := shopSys) (Q := newSys) h.completion _ _).symm
  · exact (precedence_iff (P := shopSys) (Q := newSys) h.start h.completion _ _ _).symm

theorem fields_toOldS (y : Assembly.Inst ShopFamily.family (ofShop s)) {σ : Shops.Sched y.base}
    {τ : PreemptiveShops.Sched y.base} (h : Match y.base σ τ) (hf : Shops.feasible y.base σ)
    (i : ShopProblems.FieldName) :
    (ShopProblems.family.module i).constraint (s.module i) y.base ((toOldS y).data i) σ ↔
      (ShopFamily.family.module (.field i)).constraint ((ofShop s).module (.field i)) y.base
        (y.data (.field i)) τ := by
  cases i
  · exact (shopType_iff h _).symm
  · exact (machineSets_iff h _ _).symm
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact (noWait_iff h _).symm
  · exact (transportation_iff h hf _ _).symm
  · exact (server_iff h _ _).symm
  · exact (noIdle_iff h _).symm
  · exact (batchSetups_iff h _ _).symm
  · exact release_iff (P := newSys) (Q := shopSys) (fun j => (h.start j).symm) _ _
  · exact deadlines_iff (P := newSys) (Q := shopSys) (fun j => (h.completion j).symm) _ _
  · exact precedence_iff (P := newSys) (Q := shopSys) (fun j => (h.start j).symm)
      (fun j => (h.completion j).symm) _ _ _

/--
---
conclusion: Lax434175.ShopFamily.shop_faithful
---
A non-preemptive shop schedule is a schedule with one full piece per
operation starting at an integral time.
-/
theorem shop_faithful (s : Spec ShopProblems.family) :
    SpecialCase (problem _ s) (problem ShopFamily.family (ofShop s)) ∧
      SpecialCase (problem ShopFamily.family (ofShop s)) (problem _ s) := by
  refine ⟨⟨⟨toNewS, fun x σ => toPieces x.base σ, fun x τ => ofPieces x.base τ⟩, ?_⟩,
    ⟨⟨toOldS, fun y τ => ofPieces y.base τ, fun y σ => toPieces y.base σ⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x σ ⟨hk, hc⟩
      obtain ⟨hf, hm⟩ := toPieces_feasible σ hk
      refine ⟨hf, ?_⟩
      rintro (_ | i)
      · exact hm
      · exact (fields_toNewS x (toPieces_match σ) hk i).mp (hc i)
    · rintro x σ -
      exact le_of_eq (cost_eq (P := shopSys) (Q := newSys) (toPieces_match σ).completion _ _)
    · rintro x τ ⟨hk, hc⟩
      obtain ⟨hf, h⟩ := ofPieces_back τ hk (hc .interruption)
      exact ⟨hf, fun i => (fields_toNewS x h hf i).mpr (hc (.field i))⟩
    · rintro x τ ⟨hk, hc⟩
      obtain ⟨-, h⟩ := ofPieces_back τ hk (hc .interruption)
      exact ge_of_eq (cost_eq (P := shopSys) (Q := newSys) h.completion _ _)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro y τ ⟨hk, hc⟩
      obtain ⟨hf, h⟩ := ofPieces_back τ hk (hc .interruption)
      exact ⟨hf, fun i => (fields_toOldS y h hf i).mpr (hc (.field i))⟩
    · rintro y τ ⟨hk, hc⟩
      obtain ⟨-, h⟩ := ofPieces_back τ hk (hc .interruption)
      exact le_of_eq (cost_eq (P := newSys) (Q := shopSys) (fun j => (h.completion j).symm) _ _)
    · rintro y σ ⟨hk, hc⟩
      obtain ⟨hf, hm⟩ := toPieces_feasible σ hk
      refine ⟨hf, ?_⟩
      rintro (_ | i)
      · exact hm
      · exact (fields_toOldS y (toPieces_match σ) hk i).mp (hc i)
    · rintro y σ -
      exact ge_of_eq (cost_eq (P := newSys) (Q := shopSys)
        (fun j => ((toPieces_match σ).completion j).symm) _ _)

end ShopFaithful

section PreemptiveFaithful

/-- A preemptive shop instance read in the family: no delays, no server and no
batches. -/
def toNewP {s : Spec PreemptiveShopProblems.family}
    (x : Assembly.Inst PreemptiveShopProblems.family s) :
    Assembly.Inst ShopFamily.family (ofPreemptiveShop s) where
  base := x.base
  data
    | .interruption => ()
    | .field .shopType => x.data .shopType
    | .field .machineSets => x.data .machineSets
    | .field .machineCount => x.data .machineCount
    | .field .jobCount => x.data .jobCount
    | .field .processingTimes => x.data .processingTimes
    | .field .noWait => ()
    | .field .transportation => (fun _ _ _ => 0, fun _ _ => 0)
    | .field .server => ()
    | .field .noIdle => ()
    | .field .batchSetups => ()
    | .field .releaseDates => x.data .releaseDates
    | .field .deadlines => deadlinesData pshopSys newSys _ (x.data .deadlines)
    | .field .precedence => x.data .precedence
  admitted
    | .interruption => trivial
    | .field .shopType => x.admitted .shopType
    | .field .machineSets => x.admitted .machineSets
    | .field .machineCount => x.admitted .machineCount
    | .field .jobCount => x.admitted .jobCount
    | .field .processingTimes => x.admitted .processingTimes
    | .field .noWait => trivial
    | .field .transportation => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    | .field .server => trivial
    | .field .noIdle => trivial
    | .field .batchSetups => trivial
    | .field .releaseDates =>
      release_admits (P := pshopSys) (Q := newSys) (s.module .releaseDates) ()
        (x.admitted .releaseDates)
    | .field .deadlines => trivial
    | .field .precedence => x.admitted .precedence
  objectiveData := objectiveData pshopSys newSys _ x.objectiveData
  objectiveAdmitted :=
    objective_admits (P := pshopSys) (Q := newSys) s.objective x.objectiveData x.objectiveAdmitted

/-- An instance of the family with preemption read as a preemptive shop
instance. -/
def toOldP {s : Spec PreemptiveShopProblems.family}
    (y : Assembly.Inst ShopFamily.family (ofPreemptiveShop s)) :
    Assembly.Inst PreemptiveShopProblems.family s where
  base := y.base
  data
    | .shopType => y.data (.field .shopType)
    | .machineSets => y.data (.field .machineSets)
    | .machineCount => y.data (.field .machineCount)
    | .jobCount => y.data (.field .jobCount)
    | .processingTimes => y.data (.field .processingTimes)
    | .releaseDates => y.data (.field .releaseDates)
    | .deadlines => deadlinesData newSys pshopSys _ (y.data (.field .deadlines))
    | .precedence => y.data (.field .precedence)
  admitted
    | .shopType => y.admitted (.field .shopType)
    | .machineSets => y.admitted (.field .machineSets)
    | .machineCount => y.admitted (.field .machineCount)
    | .jobCount => y.admitted (.field .jobCount)
    | .processingTimes => y.admitted (.field .processingTimes)
    | .releaseDates =>
      release_admits (P := newSys) (Q := pshopSys) (s.module .releaseDates) ()
        (y.admitted (.field .releaseDates))
    | .deadlines => trivial
    | .precedence => y.admitted (.field .precedence)
  objectiveData := objectiveData newSys pshopSys _ y.objectiveData
  objectiveAdmitted :=
    objective_admits (P := newSys) (Q := pshopSys) s.objective y.objectiveData y.objectiveAdmitted

variable {s : Spec PreemptiveShopProblems.family}

/-- Without delays, server, no-idle and batches, these fields impose
nothing. -/
theorem extras_hold (y : Assembly.Inst ShopFamily.family (ofPreemptiveShop s))
    (τ : PreemptiveShops.Sched y.base) (i : ShopProblems.FieldName)
    (hi : i = .noWait ∨ i = .transportation ∨ i = .server ∨ i = .noIdle ∨ i = .batchSetups) :
    (ShopFamily.family.module (.field i)).constraint ((ofPreemptiveShop s).module (.field i))
      y.base (y.data (.field i)) τ := by
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · intro h
    cases h
  · have ht : ∀ j k l, (y.data (.field .transportation)).1 j k l = 0 :=
      (y.admitted (.field .transportation)).1
    refine ⟨fun j k l _ => Or.inl ⟨ht j k l, ht j l k⟩, fun h => ?_⟩
    cases h
  · intro _ h
    cases h
  · intro h
    cases h
  · intro a b h
    exact absurd rfl h

theorem fields_toOldP (y : Assembly.Inst ShopFamily.family (ofPreemptiveShop s))
    (τ : PreemptiveShops.Sched y.base) :
    (∀ i, (PreemptiveShopProblems.family.module i).constraint (s.module i) y.base
      ((toOldP y).data i) τ) ↔
      ∀ i : ShopProblems.FieldName, (ShopFamily.family.module (.field i)).constraint
        ((ofPreemptiveShop s).module (.field i)) y.base (y.data (.field i)) τ := by
  constructor
  · intro H i
    cases i
    · exact H .shopType
    · exact H .machineSets
    · exact H .machineCount
    · exact H .jobCount
    · exact H .processingTimes
    · exact extras_hold y τ _ (by simp)
    · exact extras_hold y τ _ (by simp)
    · exact extras_hold y τ _ (by simp)
    · exact extras_hold y τ _ (by simp)
    · exact extras_hold y τ _ (by simp)
    · exact (release_iff (P := newSys) (Q := pshopSys) (fun _ => rfl) _ _).mp (H .releaseDates)
    · exact (deadlines_iff (P := newSys) (Q := pshopSys) (fun _ => rfl) _ _).mp (H .deadlines)
    · exact (precedence_iff (P := newSys) (Q := pshopSys) (fun _ => rfl) (fun _ => rfl) _ _ _).mp
        (H .precedence)
  · intro H i
    cases i
    · exact H .shopType
    · exact H .machineSets
    · exact H .machineCount
    · exact H .jobCount
    · exact H .processingTimes
    · exact (release_iff (P := newSys) (Q := pshopSys) (fun _ => rfl) _ _).mpr (H .releaseDates)
    · exact (deadlines_iff (P := newSys) (Q := pshopSys) (fun _ => rfl) _ _).mpr (H .deadlines)
    · exact (precedence_iff (P := newSys) (Q := pshopSys) (fun _ => rfl) (fun _ => rfl) _ _ _).mpr
        (H .precedence)

theorem fields_toNewP (x : Assembly.Inst PreemptiveShopProblems.family s)
    (τ : PreemptiveShops.Sched x.base) :
    (∀ i, (PreemptiveShopProblems.family.module i).constraint (s.module i) x.base (x.data i) τ) ↔
      ∀ i : ShopProblems.FieldName, (ShopFamily.family.module (.field i)).constraint
        ((ofPreemptiveShop s).module (.field i)) x.base ((toNewP x).data (.field i)) τ := by
  constructor
  · intro H i
    cases i
    · exact H .shopType
    · exact H .machineSets
    · exact H .machineCount
    · exact H .jobCount
    · exact H .processingTimes
    · exact extras_hold (toNewP x) τ _ (by simp)
    · exact extras_hold (toNewP x) τ _ (by simp)
    · exact extras_hold (toNewP x) τ _ (by simp)
    · exact extras_hold (toNewP x) τ _ (by simp)
    · exact extras_hold (toNewP x) τ _ (by simp)
    · exact (release_iff (P := pshopSys) (Q := newSys) (fun _ => rfl) _ _).mpr (H .releaseDates)
    · exact (deadlines_iff (P := pshopSys) (Q := newSys) (fun _ => rfl) _ _).mpr (H .deadlines)
    · exact (precedence_iff (P := pshopSys) (Q := newSys) (fun _ => rfl) (fun _ => rfl) _ _ _).mpr
        (H .precedence)
  · intro H i
    cases i
    · exact H .shopType
    · exact H .machineSets
    · exact H .machineCount
    · exact H .jobCount
    · exact H .processingTimes
    · exact (release_iff (P := pshopSys) (Q := newSys) (fun _ => rfl) _ _).mp (H .releaseDates)
    · exact (deadlines_iff (P := pshopSys) (Q := newSys) (fun _ => rfl) _ _).mp (H .deadlines)
    · exact (precedence_iff (P := pshopSys) (Q := newSys) (fun _ => rfl) (fun _ => rfl) _ _ _).mp
        (H .precedence)

/--
---
conclusion: Lax434175.ShopFamily.preemptiveShop_faithful
---
A preemptive shop schedule is a schedule with pieces in which the pieces of
every operation sum to its processing time; the fields that preemptive shops
do not have impose nothing at their value none.
-/
theorem preemptiveShop_faithful (s : Spec PreemptiveShopProblems.family) :
    SpecialCase (problem _ s) (problem ShopFamily.family (ofPreemptiveShop s)) ∧
      SpecialCase (problem ShopFamily.family (ofPreemptiveShop s)) (problem _ s) := by
  refine ⟨⟨⟨toNewP, fun _ σ => σ, fun _ τ => τ⟩, ?_⟩, ⟨⟨toOldP, fun _ τ => τ, fun _ σ => σ⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x σ ⟨hk, hc⟩
      refine ⟨⟨hk.1, hk.2.1⟩, ?_⟩
      rintro (_ | i)
      · exact hk.2.2
      · exact (fields_toNewP x σ).mp hc i
    · rintro x σ -
      exact le_of_eq (cost_eq (P := pshopSys) (Q := newSys) (σ := σ) (τ := σ) (fun _ => rfl) _ _)
    · rintro x τ ⟨hk, hc⟩
      exact ⟨⟨hk.1, hk.2, hc .interruption⟩, (fields_toNewP x τ).mpr fun i => hc (.field i)⟩
    · rintro x τ -
      exact ge_of_eq (cost_eq (P := pshopSys) (Q := newSys) (σ := τ) (τ := τ) (fun _ => rfl) _ _)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro y τ ⟨hk, hc⟩
      exact ⟨⟨hk.1, hk.2, hc .interruption⟩, (fields_toOldP y τ).mpr fun i => hc (.field i)⟩
    · rintro y τ -
      exact le_of_eq (cost_eq (P := newSys) (Q := pshopSys) (σ := τ) (τ := τ) (fun _ => rfl) _ _)
    · rintro y σ ⟨hk, hc⟩
      refine ⟨⟨hk.1, hk.2.1⟩, ?_⟩
      rintro (_ | i)
      · exact hk.2.2
      · exact (fields_toOldP y σ).mp hc i
    · rintro y σ -
      exact ge_of_eq (cost_eq (P := newSys) (Q := pshopSys) (σ := σ) (τ := σ) (fun _ => rfl) _ _)

end PreemptiveFaithful

end Lax434175Proofs.ShopFamily
