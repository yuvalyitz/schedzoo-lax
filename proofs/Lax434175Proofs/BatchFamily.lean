import Lax434175.BatchFamily
import Lax434175Proofs.BatchProblems

namespace Lax434175Proofs.BatchFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.BatchFamily
open Lax434175.Batching (Inst Capacity ProcessingTimes members)

section Soundness

theorem mode_sound : BatchFamily.mode.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint v w h _ _ _ _ := by
    change Batching.Mode at v w
    cases v <;> cases w <;> first | exact Iff.rfl | exact absurd h (by decide)

theorem capacity_sound : BatchFamily.capacity.Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : Capacity) h (x : Inst) (d : v.Data x) σ _ => by
    change (∀ k, ∑ j ∈ members σ.plain k, w.size (Capacity.embed h x d) j ≤
      w.bound (Capacity.embed h x d)) ↔ (∀ k, ∑ j ∈ members σ.plain k, v.size d j ≤ v.bound d)
    rw [Batching.bound_embed v w h x d, Batching.size_embed v w h x d]

theorem processingTimes_sound : BatchFamily.processingTimes.Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : ProcessingTimes) h (x : Inst) _ hv => by
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
conclusion: Lax434175.BatchFamily.family_sound
---
-/
theorem family_sound : BatchFamily.family.Sound where
  module
    | .mode => mode_sound
    | .field .capacity => capacity_sound
    | .field .jobCount => Counts.sound _ _
    | .field .processingTimes => processingTimes_sound
    | .field .releaseDates => ReleaseDates.sound _
    | .field .deadlines => Deadlines.sound _
    | .field .precedence => Precedence.oneMachine_sound _
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.BatchFamily.specialCase_of_le
---
-/
theorem specialCase_of_le {s t : Spec BatchFamily.family} :
    s.le t → SpecialCase (problem BatchFamily.family s) (problem BatchFamily.family t) :=
  fun h => ⟨lift BatchFamily.family family_sound h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.BatchFamily.reducible_of_reduces
---
-/
theorem reducible_of_reduces {s t : Spec BatchFamily.family} :
    Thresholds.Reduces s t →
      Reducible (problem BatchFamily.family s) (problem BatchFamily.family t) :=
  Thresholds.reducible_of_reduces family_sound.module

end Soundness

section Kernels

/-- The schedules of a machine model on batch instances. -/
structure BSys where
  Sched : Inst → Type
  feasible : (x : Inst) → Sched x → Prop
  start : (x : Inst) → Sched x → Fin x.jobs → NNRat
  completion : (x : Inst) → Sched x → Fin x.jobs → NNRat

/-- The kernel with these schedules. -/
abbrev BSys.kernel (P : BSys) : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := P.Sched
  feasible := P.feasible
  start := P.start
  completion := P.completion

/-- Batch schedules of a mode. -/
abbrev oldSys (m : Batching.Mode) : BSys where
  Sched := Batching.Sched
  feasible := Batching.feasible m
  start _ σ j := (σ.start (σ.batch j) : NNRat)
  completion x σ j := (Batching.finish m x σ (σ.batch j) : NNRat)

/-- Batch schedules with the processing times of their batches. -/
abbrev newSys : BSys where
  Sched := Sched
  feasible := BatchFamily.feasible
  start _ σ j := (σ.start (σ.batch j) : NNRat)
  completion _ σ j := (finish σ (σ.batch j) : NNRat)

example (m : Batching.Mode) : Batching.kernel m = (oldSys m).kernel := rfl
example : BatchFamily.kernel = newSys.kernel := rfl

variable {P Q : BSys} {x : Inst} {σ : P.Sched x} {τ : Q.Sched x}

theorem release_admits (v d) :
    (ReleaseDates.module P.kernel).admits v x d → (ReleaseDates.module Q.kernel).admits v x d := by
  intro h
  cases v <;> exact h

/-- Deadlines of an instance read in another machine model. -/
def deadlinesData (P Q : BSys) (v : Deadlines.Value)
    (d : (Deadlines.module P.kernel).Data v x) : (Deadlines.module Q.kernel).Data v x := by
  cases v <;> exact d

/-- Objective data of an instance read in another machine model. -/
def objectiveData (P Q : BSys) (v : Objectives.Value)
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

section Faithful

variable {m : Batching.Mode}

/-- A batch schedule of a mode with the processing times of its batches. -/
def withLengths (m : Batching.Mode) (x : Inst) (σ : Batching.Sched x) : Sched x :=
  ⟨σ.batch, σ.start, Batching.length m x σ⟩

/-- An instance of a mode read in the family. -/
def toNew {s : Spec (BatchProblems.family m)} (x : Assembly.Inst (BatchProblems.family m) s) :
    Assembly.Inst BatchFamily.family (ofSpec m s) where
  base := x.base
  data
    | .mode => ()
    | .field .capacity => x.data .capacity
    | .field .jobCount => x.data .jobCount
    | .field .processingTimes => x.data .processingTimes
    | .field .releaseDates => x.data .releaseDates
    | .field .deadlines => deadlinesData (oldSys m) newSys _ (x.data .deadlines)
    | .field .precedence => x.data .precedence
  admitted
    | .mode => trivial
    | .field .capacity => x.admitted .capacity
    | .field .jobCount => x.admitted .jobCount
    | .field .processingTimes => x.admitted .processingTimes
    | .field .releaseDates =>
      release_admits (P := oldSys m) (Q := newSys) (s.module .releaseDates) ()
        (x.admitted .releaseDates)
    | .field .deadlines => trivial
    | .field .precedence => x.admitted .precedence
  objectiveData := objectiveData (oldSys m) newSys _ x.objectiveData
  objectiveAdmitted :=
    objective_admits (P := oldSys m) (Q := newSys) s.objective x.objectiveData x.objectiveAdmitted

/-- An instance of the family read in its mode. -/
def toOld {s : Spec (BatchProblems.family m)} (y : Assembly.Inst BatchFamily.family (ofSpec m s)) :
    Assembly.Inst (BatchProblems.family m) s where
  base := y.base
  data
    | .capacity => y.data (.field .capacity)
    | .jobCount => y.data (.field .jobCount)
    | .processingTimes => y.data (.field .processingTimes)
    | .releaseDates => y.data (.field .releaseDates)
    | .deadlines => deadlinesData newSys (oldSys m) _ (y.data (.field .deadlines))
    | .precedence => y.data (.field .precedence)
  admitted
    | .capacity => y.admitted (.field .capacity)
    | .jobCount => y.admitted (.field .jobCount)
    | .processingTimes => y.admitted (.field .processingTimes)
    | .releaseDates =>
      release_admits (P := newSys) (Q := oldSys m) (s.module .releaseDates) ()
        (y.admitted (.field .releaseDates))
    | .deadlines => trivial
    | .precedence => y.admitted (.field .precedence)
  objectiveData := objectiveData newSys (oldSys m) _ y.objectiveData
  objectiveAdmitted :=
    objective_admits (P := newSys) (Q := oldSys m) s.objective y.objectiveData y.objectiveAdmitted

/-- With the processing times of its mode, a schedule completes its batches
when the batch schedule of the mode does. -/
theorem completion_eq {x : Inst} (τ : Sched x) (hm : ∀ k, τ.length k = Batching.length m x τ.plain k)
    (j : Fin x.jobs) : newSys.completion x τ j = (oldSys m).completion x τ.plain j := by
  change ((τ.start (τ.batch j) + τ.length (τ.batch j) : ℕ) : NNRat) =
    ((τ.start (τ.batch j) + Batching.length m x τ.plain (τ.batch j) : ℕ) : NNRat)
  rw [hm]

theorem feasible_iff {x : Inst} (τ : Sched x) (hm : ∀ k, τ.length k = Batching.length m x τ.plain k) :
    BatchFamily.feasible x τ ↔ Batching.feasible m x τ.plain := by
  have e : ∀ k, finish τ k = Batching.finish m x τ.plain k := fun k => by
    unfold finish Batching.finish
    rw [hm]
    rfl
  unfold BatchFamily.feasible Batching.feasible
  simp only [e]
  rfl

variable {s : Spec (BatchProblems.family m)}

theorem fields_toNew (x : Assembly.Inst (BatchProblems.family m) s) {σ : Batching.Sched x.base}
    {τ : Sched x.base} (hs : ∀ j, newSys.start x.base τ j = (oldSys m).start x.base σ j)
    (hc : ∀ j, newSys.completion x.base τ j = (oldSys m).completion x.base σ j)
    (hb : τ.plain = σ) (i : BatchProblems.FieldName) :
    ((BatchProblems.family m).module i).constraint (s.module i) x.base (x.data i) σ ↔
      (BatchFamily.family.module (.field i)).constraint ((ofSpec m s).module (.field i)) x.base
        ((toNew x).data (.field i)) τ := by
  subst hb
  cases i
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact (release_iff (P := oldSys m) (Q := newSys) hs _ _).symm
  · exact (deadlines_iff (P := oldSys m) (Q := newSys) hc _ _).symm
  · exact (precedence_iff (P := oldSys m) (Q := newSys) hs hc (fun _ => 1) _ _).symm

theorem fields_toOld (y : Assembly.Inst BatchFamily.family (ofSpec m s)) {σ : Batching.Sched y.base}
    {τ : Sched y.base} (hs : ∀ j, newSys.start y.base τ j = (oldSys m).start y.base σ j)
    (hc : ∀ j, newSys.completion y.base τ j = (oldSys m).completion y.base σ j)
    (hb : τ.plain = σ) (i : BatchProblems.FieldName) :
    ((BatchProblems.family m).module i).constraint (s.module i) y.base ((toOld y).data i) σ ↔
      (BatchFamily.family.module (.field i)).constraint ((ofSpec m s).module (.field i)) y.base
        (y.data (.field i)) τ := by
  subst hb
  cases i
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact release_iff (P := newSys) (Q := oldSys m) (fun j => (hs j).symm) _ _
  · exact deadlines_iff (P := newSys) (Q := oldSys m) (fun j => (hc j).symm) _ _
  · exact precedence_iff (P := newSys) (Q := oldSys m) (fun j => (hs j).symm)
      (fun j => (hc j).symm) (fun _ => 1) _ _

/--
---
conclusion: Lax434175.BatchFamily.faithful
---
A batch schedule of a mode, together with the processing times its batches
have in that mode, is a schedule of the family.
-/
theorem faithful (m : Batching.Mode) (s : Spec (BatchProblems.family m)) :
    SpecialCase (problem _ s) (problem BatchFamily.family (ofSpec m s)) ∧
      SpecialCase (problem BatchFamily.family (ofSpec m s)) (problem _ s) := by
  have hw : ∀ (x : Inst) (σ : Batching.Sched x),
      ∀ k, (withLengths m x σ).length k = Batching.length m x (withLengths m x σ).plain k :=
    fun _ _ _ => rfl
  refine ⟨⟨⟨toNew, fun x σ => withLengths m x.base σ, fun _ τ => τ.plain⟩, ?_⟩,
    ⟨⟨toOld, fun _ τ => τ.plain, fun y σ => withLengths m y.base σ⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x σ ⟨hk, hc⟩
      refine ⟨hk, ?_⟩
      rintro (_ | i)
      · exact hw x.base σ
      · exact (fields_toNew x (fun _ => rfl) (fun _ => rfl) rfl i).mp (hc i)
    · rintro x σ -
      exact le_of_eq (cost_eq (P := oldSys m) (Q := newSys) (σ := σ) (τ := withLengths m _ σ)
        (fun _ => rfl) _ _)
    · rintro x τ ⟨hk, hc⟩
      have hm := hc .mode
      exact ⟨(feasible_iff τ hm).mp hk,
        fun i => (fields_toNew x (fun _ => rfl) (completion_eq τ hm) rfl i).mpr (hc (.field i))⟩
    · rintro x τ ⟨-, hc⟩
      exact ge_of_eq (cost_eq (P := oldSys m) (Q := newSys) (completion_eq τ (hc .mode)) _ _)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro y τ ⟨hk, hc⟩
      have hm := hc .mode
      exact ⟨(feasible_iff τ hm).mp hk,
        fun i => (fields_toOld y (fun _ => rfl) (completion_eq τ hm) rfl i).mpr (hc (.field i))⟩
    · rintro y τ ⟨-, hc⟩
      exact le_of_eq (cost_eq (P := newSys) (Q := oldSys m)
        (fun j => (completion_eq τ (hc .mode) j).symm) _ _)
    · rintro y σ ⟨hk, hc⟩
      refine ⟨hk, ?_⟩
      rintro (_ | i)
      · exact hw y.base σ
      · exact (fields_toOld y (fun _ => rfl) (fun _ => rfl) rfl i).mp (hc i)
    · rintro y σ -
      exact ge_of_eq (cost_eq (P := newSys) (Q := oldSys m) (σ := withLengths m _ σ) (τ := σ)
        (fun _ => rfl) _ _)

end Faithful

end Lax434175Proofs.BatchFamily
