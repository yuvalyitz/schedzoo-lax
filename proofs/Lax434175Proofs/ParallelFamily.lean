import Lax434175.ParallelFamily
import Lax434175Proofs.ParallelProblems
import Lax434175Proofs.Interruption
import Lax434175Proofs.Restarts

namespace Lax434175Proofs.ParallelFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.ParallelMachines Lax434175.ParallelFamily
open Lax434175

/-- The schedules of a machine model on parallel-machine instances. -/
structure Sys where
  Sched : Inst → Type
  feasible : (x : Inst) → Sched x → Prop
  start : (x : Inst) → Sched x → Fin x.jobs → NNRat
  completion : (x : Inst) → Sched x → Fin x.jobs → NNRat
  uses : (x : Inst) → Sched x → Fin x.jobs → Finset (Fin x.machines) → Prop

/-- The machine model with these schedules. -/
abbrev Sys.model (P : Sys) : Model where
  kernel :=
    { Inst := Inst, jobs := Inst.jobs, release := Inst.r, Sched := P.Sched,
      feasible := P.feasible, start := P.start, completion := P.completion }
  inst x := x
  jobs_eq _ := rfl
  uses := P.uses

/-- The problems of a machine model with these schedules. -/
abbrev fam (P : Sys) := ParallelProblems.family P.model

/-- Two schedules of an instance in two machine models have the same start and
completion times, and the second uses no set of machines the first does not. -/
structure Agree (P Q : Sys) (x : Inst) (σ : P.Sched x) (τ : Q.Sched x) : Prop where
  start : ∀ j, Q.start x τ j = P.start x σ j
  completion : ∀ j, Q.completion x τ j = P.completion x σ j
  uses : ∀ j S, Q.uses x τ j S → P.uses x σ j S

section Transfer

variable {P Q : Sys} {x : Inst} {σ : P.Sched x} {τ : Q.Sched x}

theorem release_transfer (h : Agree P Q x σ τ) (v d) :
    (ReleaseDates.module P.model.kernel).constraint v x d σ →
      (ReleaseDates.module Q.model.kernel).constraint v x d τ := by
  intro hc j
  change (x.r j : NNRat) ≤ Q.start x τ j
  rw [h.start j]
  exact hc j

theorem release_admits (v d) :
    (ReleaseDates.module P.model.kernel).admits v x d →
      (ReleaseDates.module Q.model.kernel).admits v x d := by
  intro h
  cases v <;> exact h

/-- Deadlines of an instance read in another machine model. -/
def deadlinesData (P Q : Sys) (v : Deadlines.Value)
    (d : (Deadlines.module P.model.kernel).Data v x) :
    (Deadlines.module Q.model.kernel).Data v x := by
  cases v <;> exact d

theorem deadlines_transfer (h : Agree P Q x σ τ) (v d) :
    (Deadlines.module P.model.kernel).constraint v x d σ →
      (Deadlines.module Q.model.kernel).constraint v x (deadlinesData P Q v d) τ := by
  intro hc j
  have hj := hc j
  cases v <;>
  · change Deadlines.Within (Q.completion x τ j) _
    rw [h.completion j]
    exact hj

theorem deadlines_transfer' (h : Agree P Q x σ τ) (v d) :
    (Deadlines.module P.model.kernel).constraint v x (deadlinesData Q P v d) σ →
      (Deadlines.module Q.model.kernel).constraint v x d τ := by
  intro hc j
  have hj := hc j
  cases v <;>
  · change Deadlines.Within (Q.completion x τ j) _
    rw [h.completion j]
    exact hj

theorem precedence_transfer (h : Agree P Q x σ τ) (v d) :
    (Precedence.module P.model.kernel (machines P.model)).constraint v x d σ →
      (Precedence.module Q.model.kernel (machines Q.model)).constraint v x d τ := by
  intro hc i j hv
  change (Q.completion x τ i : ℚ) + _ ≤ (Q.start x τ j : ℚ)
  rw [h.completion i, h.start j]
  exact hc i j hv

theorem forbidden_transfer (h : Agree P Q x σ τ) (v d) :
    (ForbiddenTimes.module P.model.kernel).constraint v x d σ →
      (ForbiddenTimes.module Q.model.kernel).constraint v x d τ := by
  intro hc t ht j
  change Q.start x τ j ≠ _ ∧ Q.completion x τ j ≠ _
  rw [h.start j, h.completion j]
  exact hc t ht j

theorem machineSets_transfer (h : Agree P Q x σ τ) (v d) :
    (MachineSets.module P.model).constraint v x d σ →
      (MachineSets.module Q.model).constraint v x d τ :=
  fun hc j S hu => hc j S (h.uses j S hu)

theorem communicationDelays_transfer (h : Agree P Q x σ τ) (v d) :
    (CommunicationDelays.module P.model).constraint v x d σ →
      (CommunicationDelays.module Q.model).constraint v x d τ := by
  intro hc i j c hv S S' hS hS' hne
  change (Q.completion x τ i : ℚ) + (c : ℚ) ≤ (Q.start x τ j : ℚ)
  rw [h.completion i, h.start j]
  exact hc i j c hv S S' (h.uses i S hS) (h.uses j S' hS') hne

theorem servers_transfer (h : Agree P Q x σ τ) (v d) :
    (Servers.parallel P.model).constraint v x d σ →
      (Servers.parallel Q.model).constraint v x d τ := by
  intro hc s hs
  obtain ⟨h1, h2, h3⟩ := hc s hs
  have hst : (fun j => (Q.start x τ j : ℚ)) = fun j => (P.start x σ j : ℚ) :=
    funext fun j => by rw [h.start j]
  have hco : (fun j => (Q.completion x τ j : ℚ)) = fun j => (P.completion x σ j : ℚ) :=
    funext fun j => by rw [h.completion j]
  change Servers.Served (fun j => (Q.start x τ j : ℚ)) (fun j => (Q.completion x τ j : ℚ)) _ _ s
  rw [hst, hco]
  refine ⟨h1, h2, fun a b hab hsh => h3 a b hab ?_⟩
  obtain ⟨S, S', hS, hS', hd⟩ := hsh
  exact ⟨S, S', h.uses _ S hS, h.uses _ S' hS', hd⟩

/-- Objective data of an instance read in another machine model. -/
def objectiveData (P Q : Sys) (v : Objectives.Value)
    (d : Objectives.Data P.model.kernel v x) : Objectives.Data Q.model.kernel v x := by
  cases v <;> exact d

theorem objective_admits (v d) :
    Objectives.admits (K := P.model.kernel) v x d →
      Objectives.admits (K := Q.model.kernel) v x (objectiveData P Q v d) := by
  intro ha
  cases v <;> exact ha

theorem cost_transfer (h : ∀ j, Q.completion x τ j = P.completion x σ j) (v d) :
    Objectives.cost (K := Q.model.kernel) v x (objectiveData P Q v d) τ =
      Objectives.cost (K := P.model.kernel) v x d σ := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, h] <;> rfl

end Transfer

section Instances

variable {P Q : Sys}

/-- An instance of one machine model read in another. -/
def transInst (P Q : Sys) {s : Spec (fam P)} (x : Assembly.Inst (fam P) s) :
    Assembly.Inst (fam Q) (transSpec s) where
  base := x.base
  data
    | .environment => x.data .environment
    | .machineCount => x.data .machineCount
    | .jobCount => x.data .jobCount
    | .processingTimes => x.data .processingTimes
    | .machineSets => x.data .machineSets
    | .releaseDates => x.data .releaseDates
    | .deadlines => deadlinesData P Q _ (x.data .deadlines)
    | .precedence => x.data .precedence
    | .communicationDelays => x.data .communicationDelays
    | .server => x.data .server
    | .forbiddenTimes => x.data .forbiddenTimes
    | .encoding => x.data .encoding
  admitted
    | .environment => x.admitted .environment
    | .machineCount => x.admitted .machineCount
    | .jobCount => x.admitted .jobCount
    | .processingTimes => x.admitted .processingTimes
    | .machineSets => x.admitted .machineSets
    | .releaseDates =>
      release_admits (P := P) (Q := Q) (s.module .releaseDates) () (x.admitted .releaseDates)
    | .deadlines => trivial
    | .precedence => x.admitted .precedence
    | .communicationDelays => x.admitted .communicationDelays
    | .server => x.admitted .server
    | .forbiddenTimes => x.admitted .forbiddenTimes
    | .encoding => x.admitted .encoding
  objectiveData := objectiveData P Q _ x.objectiveData
  objectiveAdmitted := objective_admits _ _ x.objectiveAdmitted

theorem transInst_constraints {s : Spec (fam P)} (x : Assembly.Inst (fam P) s)
    {σ : P.Sched x.base} {τ : Q.Sched x.base} (h : Agree P Q x.base σ τ)
    (hc : ∀ i, ((fam P).module i).constraint (s.module i) x.base (x.data i) σ) :
    ∀ i, ((fam Q).module i).constraint ((transSpec s).module i) x.base
      ((transInst P Q x).data i) τ := by
  intro i
  cases i
  · trivial
  · trivial
  · trivial
  · trivial
  · exact machineSets_transfer h _ _ (hc .machineSets)
  · exact release_transfer h _ _ (hc .releaseDates)
  · exact deadlines_transfer h _ _ (hc .deadlines)
  · exact precedence_transfer h _ _ (hc .precedence)
  · exact communicationDelays_transfer h _ _ (hc .communicationDelays)
  · exact servers_transfer h _ _ (hc .server)
  · exact forbidden_transfer h _ _ (hc .forbiddenTimes)
  · trivial

theorem transInst_constraints' {s : Spec (fam Q)} (y : Assembly.Inst (fam Q) s)
    {σ : P.Sched y.base} {τ : Q.Sched y.base} (h : Agree P Q y.base σ τ)
    (hc : ∀ i, ((fam P).module i).constraint ((transSpec s).module i) y.base
      ((transInst Q P y).data i) σ) :
    ∀ i, ((fam Q).module i).constraint (s.module i) y.base (y.data i) τ := by
  intro i
  cases i
  · trivial
  · trivial
  · trivial
  · trivial
  · exact machineSets_transfer h _ _ (hc .machineSets)
  · exact release_transfer h _ _ (hc .releaseDates)
  · exact deadlines_transfer' h _ _ (hc .deadlines)
  · exact precedence_transfer h _ _ (hc .precedence)
  · exact communicationDelays_transfer h _ _ (hc .communicationDelays)
  · exact servers_transfer h _ _ (hc .server)
  · exact forbidden_transfer h _ _ (hc .forbiddenTimes)
  · trivial

end Instances

/-- The schedules made of pieces. -/
abbrev pieces : Sys where
  Sched := Preemptive.Sched
  feasible _ σ := Interruption.feasible σ
  start := Preemptive.start
  completion := Preemptive.completion
  uses _ σ j S := ∃ q ∈ Preemptive.piecesOf σ j, q.machines = S

example : Interruption.model = pieces.model := rfl

section Faithful

variable (P : Sys) (m : Interruption.Mode)

/-- An instance of a machine model read in the family. -/
def toNew {s : Spec (fam P)} (x : Assembly.Inst (fam P) s) :
    Assembly.Inst family (ofSpec m s) where
  base := x.base
  data
    | .interruption => ()
    | .field i => (transInst P pieces x).data i
  admitted
    | .interruption => trivial
    | .field i => (transInst P pieces x).admitted i
  objectiveData := (transInst P pieces x).objectiveData
  objectiveAdmitted := (transInst P pieces x).objectiveAdmitted

/-- An instance of the family read in a machine model. -/
def toOld {s : Spec (fam P)} (y : Assembly.Inst family (ofSpec m s)) :
    Assembly.Inst (fam P) s where
  base := y.base
  data
    | .environment => y.data (.field .environment)
    | .machineCount => y.data (.field .machineCount)
    | .jobCount => y.data (.field .jobCount)
    | .processingTimes => y.data (.field .processingTimes)
    | .machineSets => y.data (.field .machineSets)
    | .releaseDates => y.data (.field .releaseDates)
    | .deadlines => deadlinesData pieces P _ (y.data (.field .deadlines))
    | .precedence => y.data (.field .precedence)
    | .communicationDelays => y.data (.field .communicationDelays)
    | .server => y.data (.field .server)
    | .forbiddenTimes => y.data (.field .forbiddenTimes)
    | .encoding => y.data (.field .encoding)
  admitted
    | .environment => y.admitted (.field .environment)
    | .machineCount => y.admitted (.field .machineCount)
    | .jobCount => y.admitted (.field .jobCount)
    | .processingTimes => y.admitted (.field .processingTimes)
    | .machineSets => y.admitted (.field .machineSets)
    | .releaseDates =>
      release_admits (P := pieces) (Q := P) (s.module .releaseDates) ()
        (y.admitted (.field .releaseDates))
    | .deadlines => trivial
    | .precedence => y.admitted (.field .precedence)
    | .communicationDelays => y.admitted (.field .communicationDelays)
    | .server => y.admitted (.field .server)
    | .forbiddenTimes => y.admitted (.field .forbiddenTimes)
    | .encoding => y.admitted (.field .encoding)
  objectiveData := objectiveData pieces P _ y.objectiveData
  objectiveAdmitted := objective_admits _ _ y.objectiveAdmitted

variable {P m}

theorem toOld_constraints {s : Spec (fam P)} (y : Assembly.Inst family (ofSpec m s))
    {τ : Preemptive.Sched y.base} {σ : P.Sched y.base} (h : Agree pieces P y.base τ σ)
    (hc : ∀ i, (family.module i).constraint ((ofSpec m s).module i) y.base (y.data i) τ) :
    ∀ i, ((fam P).module i).constraint (s.module i) y.base ((toOld P m y).data i) σ := by
  intro i
  cases i
  · trivial
  · trivial
  · trivial
  · trivial
  · exact machineSets_transfer h _ _ (hc (.field .machineSets))
  · exact release_transfer h _ _ (hc (.field .releaseDates))
  · exact deadlines_transfer h _ _ (hc (.field .deadlines))
  · exact precedence_transfer h _ _ (hc (.field .precedence))
  · exact communicationDelays_transfer h _ _ (hc (.field .communicationDelays))
  · exact servers_transfer h _ _ (hc (.field .server))
  · exact forbidden_transfer h _ _ (hc (.field .forbiddenTimes))
  · trivial

theorem toOld_constraints' {s : Spec (fam P)} (y : Assembly.Inst family (ofSpec m s))
    {σ : P.Sched y.base} {τ : Preemptive.Sched y.base} (h : Agree P pieces y.base σ τ)
    (hc : ∀ i, ((fam P).module i).constraint (s.module i) y.base ((toOld P m y).data i) σ)
    (hm : m.holds y.base τ) :
    ∀ i, (family.module i).constraint ((ofSpec m s).module i) y.base (y.data i) τ := by
  intro i
  rcases i with _ | i
  · exact hm
  cases i
  · trivial
  · trivial
  · trivial
  · trivial
  · exact machineSets_transfer h _ _ (hc .machineSets)
  · exact release_transfer h _ _ (hc .releaseDates)
  · exact deadlines_transfer' h _ _ (hc .deadlines)
  · exact precedence_transfer h _ _ (hc .precedence)
  · exact communicationDelays_transfer h _ _ (hc .communicationDelays)
  · exact servers_transfer h _ _ (hc .server)
  · exact forbidden_transfer h _ _ (hc .forbiddenTimes)
  · trivial

/-- The embedding into the family is sound. -/
theorem toNew_sound (s : Spec (fam P))
    (fw : ∀ x, P.Sched x → Preemptive.Sched x) (bw : ∀ x, Preemptive.Sched x → P.Sched x)
    (hfw : ∀ x σ, P.feasible x σ →
      Interruption.feasible (fw x σ) ∧ m.holds x (fw x σ) ∧ Agree P pieces x σ (fw x σ))
    (hbw : ∀ x τ, Interruption.feasible τ → m.holds x τ →
      P.feasible x (bw x τ) ∧ Agree pieces P x τ (bw x τ)) :
    (⟨toNew P m, fun x σ => fw x.base σ, fun x τ => bw x.base τ⟩ :
      Embedding (problem (fam P) s) (problem family (ofSpec m s))).Sound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x σ ⟨hk, hc⟩
    obtain ⟨hf, hm, h⟩ := hfw _ σ hk
    refine ⟨hf, ?_⟩
    rintro (_ | i)
    · exact hm
    · exact transInst_constraints x h hc i
  · rintro x σ ⟨hk, -⟩
    exact le_of_eq (cost_transfer (hfw _ σ hk).2.2.completion _ _)
  · rintro x τ ⟨hk, hc⟩
    obtain ⟨hf, h⟩ := hbw _ τ hk (hc .interruption)
    exact ⟨hf, transInst_constraints' x h (fun i => hc (.field i))⟩
  · rintro x τ ⟨hk, hc⟩
    obtain ⟨-, h⟩ := hbw _ τ hk (hc .interruption)
    exact ge_of_eq (cost_transfer (fun j => (h.completion j).symm) _ _)

/-- A machine model whose schedules translate to schedules with pieces of a
way of interruption, and back, keeping start times, completion times and the
sets of machines used, describes the same problems as the family. -/
theorem faithful (s : Spec (fam P))
    (fw : ∀ x, P.Sched x → Preemptive.Sched x) (bw : ∀ x, Preemptive.Sched x → P.Sched x)
    (hfw : ∀ x σ, P.feasible x σ →
      Interruption.feasible (fw x σ) ∧ m.holds x (fw x σ) ∧ Agree P pieces x σ (fw x σ))
    (hbw : ∀ x τ, Interruption.feasible τ → m.holds x τ →
      P.feasible x (bw x τ) ∧ Agree pieces P x τ (bw x τ)) :
    SpecialCase (problem (fam P) s) (problem family (ofSpec m s)) ∧
      SpecialCase (problem family (ofSpec m s)) (problem (fam P) s) := by
  refine ⟨⟨_, toNew_sound s fw bw hfw hbw⟩,
    ⟨⟨toOld P m, fun y τ => bw y.base τ, fun y σ => fw y.base σ⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro y τ ⟨hk, hc⟩
      obtain ⟨hf, h⟩ := hbw _ τ hk (hc .interruption)
      exact ⟨hf, toOld_constraints y h hc⟩
    · rintro y τ ⟨hk, hc⟩
      exact le_of_eq (cost_transfer (hbw _ τ hk (hc .interruption)).2.completion _ _)
    · rintro y σ ⟨hk, hc⟩
      obtain ⟨hf, hm, h⟩ := hfw _ σ hk
      exact ⟨hf, toOld_constraints' y h hc hm⟩
    · rintro y σ ⟨hk, -⟩
      exact ge_of_eq (cost_transfer (fun j => ((hfw _ σ hk).2.2.completion j).symm) _ _)

end Faithful

/-- Preemptive schedules. -/
abbrev preemptiveSys : Sys where
  Sched := Preemptive.Sched
  feasible := Preemptive.feasible
  start := Preemptive.start
  completion := Preemptive.completion
  uses _ σ j S := ∃ q ∈ Preemptive.piecesOf σ j, q.machines = S

/--
---
conclusion: Lax434175.ParallelFamily.preemptive_faithful
---
A preemptive schedule is a schedule with pieces in which every job is
completed.
-/
theorem preemptive_faithful (s : Spec ParallelProblems.preemptive) :
    SpecialCase (problem _ s) (problem family (ofSpec .pmtn s)) ∧
      SpecialCase (problem family (ofSpec .pmtn s)) (problem _ s) :=
  faithful (P := preemptiveSys) s (fun _ σ => σ) (fun _ τ => τ)
    (fun _ _ hf => ⟨⟨hf.1, hf.2.1⟩, hf.2.2, ⟨fun _ => rfl, fun _ => rfl, fun _ _ h => h⟩⟩)
    (fun _ _ hf hm => ⟨⟨hf.1, hf.2, hm⟩, ⟨fun _ => rfl, fun _ => rfl, fun _ _ h => h⟩⟩)

section Lists

open Preemptive

theorem finRange_filter_eq (n : ℕ) (j : Fin n) :
    (List.finRange n).filter (fun i => decide (i = j)) = [j] := by
  have h := List.filter_eq (l := List.finRange n) j
  rw [List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange j)] at h
  simpa [beq_iff_eq] using h

/-- In a pairwise related list, two different members are related one way or
the other. -/
theorem pairwise_either {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact Or.inl (h.1 b hb')
    · exact Or.inr (h.1 a ha')
    · exact pairwise_either h.2 ha' hb' hab

/-- Two different pieces of a feasible schedule that share a machine or a job
do not overlap. -/
theorem apart_of_feasible {x : Inst} {σ : Sched x} (hp : σ.pieces.Pairwise
      (fun a b => (¬ Disjoint a.machines b.machines ∨ a.job = b.job) → Apart a b))
    {a b : Piece x} (ha : a ∈ σ.pieces) (hb : b ∈ σ.pieces) (hab : a ≠ b)
    (h : ¬ Disjoint a.machines b.machines ∨ a.job = b.job) : Apart a b := by
  rcases pairwise_either hp ha hb hab with h' | h'
  · exact h' h
  · have h'' : ¬ Disjoint b.machines a.machines ∨ b.job = a.job := by
      rcases h with h | h
      · exact Or.inl fun hd => h hd.symm
      · exact Or.inr h.symm
    rcases h' h'' with h3 | h3
    · exact Or.inr h3
    · exact Or.inl h3

theorem getD_max_eq (l : List NNRat) (a : NNRat) (ha : a ∈ l) (h : ∀ b ∈ l, b ≤ a) :
    (l.max?).getD 0 = a := by
  apply le_antisymm _ (Preemptive.le_max_getD l a ha)
  cases hm : l.max? with
  | none => simp [List.max?_eq_none_iff.mp hm] at ha
  | some b => exact h b (List.max?_mem hm)

theorem getD_min_eq (l : List NNRat) (a : NNRat) (ha : a ∈ l) (h : ∀ b ∈ l, a ≤ b) :
    (l.min?).getD 0 = a := by
  apply le_antisymm (Preemptive.min_getD_le l a ha)
  cases hm : l.min? with
  | none => simp [List.min?_eq_none_iff.mp hm] at ha
  | some b => exact h b (List.min?_mem hm)

theorem getD_min_mem (l : List NNRat) (h : l ≠ []) : (l.min?).getD 0 ∈ l := by
  cases hm : l.min? with
  | none => exact absurd (List.min?_eq_none_iff.mp hm) h
  | some b => exact List.min?_mem hm

theorem mem_piecesOf {x : Inst} {σ : Sched x} {j : Fin x.jobs} {q : Piece x} :
    q ∈ piecesOf σ j ↔ q ∈ σ.pieces ∧ q.job = j := by
  unfold piecesOf
  simp

theorem start_single {x : Inst} {σ : Sched x} {j : Fin x.jobs} {q : Piece x}
    (h : piecesOf σ j = [q]) : start x σ j = q.start := by
  unfold start
  rw [h]
  rfl

theorem completion_single {x : Inst} {σ : Sched x} {j : Fin x.jobs} {q : Piece x}
    (h : piecesOf σ j = [q]) : completion x σ j = q.finish := by
  unfold completion
  rw [h]
  rfl

end Lists

section Restarts

open Preemptive Lax434175.Restarts

/-- Schedules with restarts. -/
abbrev restartsSys : Sys where
  Sched := Preemptive.Sched
  feasible := Restarts.feasible
  start := Preemptive.start
  completion := Restarts.completion
  uses _ σ j S := ∃ q ∈ piecesOf σ j, q.machines = S

/-- A complete piece of a job ends at its completion time, and no complete
piece ends earlier. -/
theorem first_complete {x : Inst} (σ : Sched x) (j : Fin x.jobs)
    (hne : completePieces σ j ≠ []) :
    ∃ q ∈ completePieces σ j, q.finish = Restarts.completion x σ j ∧
      ∀ q' ∈ completePieces σ j, Restarts.completion x σ j ≤ q'.finish := by
  cases hm : ((completePieces σ j).map Piece.finish).min? with
  | none =>
    rw [List.min?_eq_none_iff, List.map_eq_nil_iff] at hm
    exact absurd hm hne
  | some c =>
    have hC : Restarts.completion x σ j = c := by
      unfold Restarts.completion
      rw [hm]
      rfl
    obtain ⟨hc, hall⟩ := List.min?_eq_some_iff.mp hm
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    exact ⟨q, hq, hC.symm, fun q' hq' => hC ▸ hall _ (List.mem_map.mpr ⟨q', hq', rfl⟩)⟩

theorem mem_completePieces {x : Inst} {σ : Sched x} {j : Fin x.jobs} {q : Piece x} :
    q ∈ completePieces σ j ↔ q ∈ piecesOf σ j ∧ Complete q := by
  unfold completePieces
  simp

/-- The pieces of a schedule with restarts that end no later than the
completion of their job. -/
def trim (x : Inst) (σ : Sched x) : Sched x :=
  ⟨σ.pieces.filter (fun q => decide (q.finish ≤ Restarts.completion x σ q.job))⟩

theorem mem_trim {x : Inst} {σ : Sched x} {j : Fin x.jobs} {q : Piece x} :
    q ∈ piecesOf (trim x σ) j ↔ q ∈ piecesOf σ j ∧ q.finish ≤ Restarts.completion x σ j := by
  rw [mem_piecesOf, mem_piecesOf]
  unfold trim
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h3⟩, h3 ▸ h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨⟨h1, h3 ▸ h2⟩, h3⟩

theorem trim_forth {x : Inst} (σ : Sched x) (hf : Restarts.feasible x σ) :
    Interruption.feasible (trim x σ) ∧ Interruption.Mode.restarts.holds x (trim x σ) ∧
      Agree restartsSys pieces x σ (trim x σ) := by
  obtain ⟨hn, hp, hc⟩ := hf
  have key : ∀ j, ∃ q ∈ piecesOf (trim x σ) j, Complete q ∧
      q.finish = Restarts.completion x σ j ∧
      ∀ q' ∈ piecesOf (trim x σ) j, q'.finish ≤ q.finish ∧ (Complete q' → q'.finish = q.finish) := by
    intro j
    obtain ⟨q, hq, hqC, hmin⟩ := first_complete σ j (hc j)
    have hq' := mem_completePieces.mp hq
    refine ⟨q, mem_trim.mpr ⟨hq'.1, hqC.le⟩, hq'.2, hqC, fun q' hq'' => ?_⟩
    obtain ⟨h1, h2⟩ := mem_trim.mp hq''
    refine ⟨hqC ▸ h2, fun hcq => ?_⟩
    have := hmin q' (mem_completePieces.mpr ⟨h1, hcq⟩)
    rw [hqC]
    exact le_antisymm h2 this
  refine ⟨⟨fun q hq => hn q (List.mem_of_mem_filter hq), hp.filter _⟩, ?_, ?_⟩
  · intro j
    obtain ⟨q, hq, hcq, -, hall⟩ := key j
    exact ⟨q, hq, hcq, hall⟩
  · refine ⟨fun j => ?_, fun j => ?_, fun j S ⟨q, hq, hS⟩ => ⟨q, (mem_trim.mp hq).1, hS⟩⟩
    · -- the first piece of a job is kept or starts after the job is complete
      obtain ⟨qs, hqs, -, hqsC, -⟩ := key j
      have hne : (piecesOf (trim x σ) j).map Piece.start ≠ [] := by
        simpa using List.ne_nil_of_mem hqs
      obtain ⟨q1, hq1, h1⟩ := List.mem_map.mp (getD_min_mem _ hne)
      have hq1' := (mem_trim.mp hq1).1
      change (((piecesOf (trim x σ) j).map Piece.start).min?).getD 0 =
        (((piecesOf σ j).map Piece.start).min?).getD 0
      apply le_antisymm _ (h1 ▸ Preemptive.min_getD_le _ _ (List.mem_map.mpr ⟨q1, hq1', rfl⟩))
      have hne' : (piecesOf σ j).map Piece.start ≠ [] := by
        simpa using List.ne_nil_of_mem hq1'
      obtain ⟨q0, hq0, h0⟩ := List.mem_map.mp (getD_min_mem _ hne')
      rw [← h0]
      by_cases hk : q0.finish ≤ Restarts.completion x σ j
      · exact Preemptive.min_getD_le _ _ (List.mem_map.mpr ⟨q0, mem_trim.mpr ⟨hq0, hk⟩, rfl⟩)
      · have hqs' := (mem_trim.mp hqs).1
        have hne0 : q0 ≠ qs := fun h => hk (h ▸ (mem_trim.mp hqs).2)
        have hj0 := (mem_piecesOf.mp hq0).2
        have hjs := (mem_piecesOf.mp hqs').2
        rcases apart_of_feasible hp (mem_piecesOf.mp hq0).1 (mem_piecesOf.mp hqs').1 hne0
            (Or.inr (hj0.trans hjs.symm)) with h | h
        · exact absurd (lt_of_le_of_lt (le_trans h (Preemptive.start_le_finish qs))
            (hqsC ▸ not_le.mp hk)) (lt_irrefl _)
        · exact le_trans (Preemptive.min_getD_le _ _ (List.mem_map.mpr ⟨qs, hqs, rfl⟩))
            (le_trans (Preemptive.start_le_finish qs) h)
    · obtain ⟨qs, hqs, -, hqsC, hall⟩ := key j
      change (((piecesOf (trim x σ) j).map Piece.finish).max?).getD 0 = _
      rw [getD_max_eq _ qs.finish (List.mem_map.mpr ⟨qs, hqs, rfl⟩) (fun b hb => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
        exact (hall q' hq').1), hqsC]

theorem restarts_back {x : Inst} (τ : Sched x) (hf : Interruption.feasible τ)
    (hm : Interruption.Mode.restarts.holds x τ) :
    Restarts.feasible x τ ∧ Agree pieces restartsSys x τ τ := by
  refine ⟨⟨hf.1, hf.2, fun j => ?_⟩, fun _ => rfl, fun j => ?_, fun _ _ h => h⟩
  · obtain ⟨q, hq, hcq, -⟩ := hm j
    exact List.ne_nil_of_mem (mem_completePieces.mpr ⟨hq, hcq⟩)
  · obtain ⟨q, hq, hcq, hall⟩ := hm j
    change (((completePieces τ j).map Piece.finish).min?).getD 0 =
      (((piecesOf τ j).map Piece.finish).max?).getD 0
    rw [getD_max_eq _ q.finish (List.mem_map.mpr ⟨q, hq, rfl⟩) (fun b hb => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
        exact (hall q' hq').1)]
    apply getD_min_eq _ _ (List.mem_map.mpr ⟨q, mem_completePieces.mpr ⟨hq, hcq⟩, rfl⟩)
    intro b hb
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
    have h' := mem_completePieces.mp hq'
    exact ((hall q' h'.1).2 h'.2).ge

/--
---
conclusion: Lax434175.ParallelFamily.restarts_faithful
---
Dropping the pieces of a job that end after its first complete piece turns a
schedule with restarts into one whose last piece is complete.
-/
theorem restarts_faithful (s : Spec ParallelProblems.restarts) :
    SpecialCase (problem _ s) (problem family (ofSpec .restarts s)) ∧
      SpecialCase (problem family (ofSpec .restarts s)) (problem _ s) :=
  faithful (P := restartsSys) s trim (fun _ τ => τ)
    (fun _ σ hf => trim_forth σ hf) (fun _ τ hf hm => restarts_back τ hf hm)

end Restarts

section Nonpreemptive

open Preemptive

/-- Non-preemptive schedules. -/
abbrev nonpreemptiveSys : Sys where
  Sched := Nonpreemptive.Sched
  feasible := Nonpreemptive.feasible
  start _ σ j := (σ.start j : NNRat)
  completion x σ j := (Nonpreemptive.completion x σ j : NNRat)
  uses _ σ j S := σ.machines j = S

/-- The piece of a job in a non-preemptive schedule. -/
def piece {x : Inst} (σ : Nonpreemptive.Sched x) (j : Fin x.jobs) : Piece x :=
  ⟨j, σ.machines j, (σ.start j : NNRat), (duration x j (σ.machines j) : NNRat)⟩

/-- A non-preemptive schedule as a schedule with pieces. -/
def toPieces (x : Inst) (σ : Nonpreemptive.Sched x) : Sched x := ⟨List.ofFn (piece σ)⟩

theorem piecesOf_toPieces {x : Inst} (σ : Nonpreemptive.Sched x) (j : Fin x.jobs) :
    piecesOf (toPieces x σ) j = [piece σ j] := by
  unfold piecesOf toPieces
  rw [List.ofFn_eq_map, List.filter_map]
  have h : ((fun q : Piece x => decide (q.job = j)) ∘ piece σ) = fun i => decide (i = j) := rfl
  rw [h, finRange_filter_eq]
  rfl

theorem finish_piece {x : Inst} (σ : Nonpreemptive.Sched x) (j : Fin x.jobs) :
    (piece σ j).finish = (Nonpreemptive.completion x σ j : NNRat) := by
  simp [Piece.finish, piece, Nonpreemptive.completion]

theorem toPieces_forth {x : Inst} (σ : Nonpreemptive.Sched x) (hf : Nonpreemptive.feasible x σ) :
    Interruption.feasible (toPieces x σ) ∧ Interruption.Mode.none.holds x (toPieces x σ) ∧
      Agree nonpreemptiveSys pieces x σ (toPieces x σ) := by
  obtain ⟨hn, hd⟩ := hf
  refine ⟨⟨fun q hq => ?_, ?_⟩, fun j => ⟨piece σ j, piecesOf_toPieces σ j, rfl, σ.start j, rfl⟩,
    fun j => ?_, fun j => ?_, fun j S ⟨q, hq, hS⟩ => ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hn j
  · refine List.pairwise_ofFn.mpr fun i j hij hc => ?_
    have hne : i ≠ j := ne_of_lt hij
    have hm : ¬ Disjoint (σ.machines i) (σ.machines j) := by
      rcases hc with hc | hc
      · exact hc
      · exact absurd hc hne
    unfold Apart
    rw [finish_piece, finish_piece]
    rcases hd i j hne hm with h | h
    · exact Or.inl (show _ ≤ ((σ.start j : ℕ) : NNRat) by exact_mod_cast h)
    · exact Or.inr (show _ ≤ ((σ.start i : ℕ) : NNRat) by exact_mod_cast h)
  · exact start_single (piecesOf_toPieces σ j)
  · change completion x (toPieces x σ) j = (Nonpreemptive.completion x σ j : NNRat)
    rw [completion_single (piecesOf_toPieces σ j), finish_piece]
  · rw [piecesOf_toPieces, List.mem_singleton] at hq
    subst hq
    exact hS

/-- A schedule with pieces read as a non-preemptive schedule: every job is
processed by its first piece. -/
noncomputable def ofPieces (x : Inst) (τ : Sched x) : Nonpreemptive.Sched x where
  machines j := (((piecesOf τ j).head?).map Piece.machines).getD ∅
  start j := Classical.epsilon fun n : ℕ => ((piecesOf τ j).head?).map Piece.start = some (n : NNRat)

theorem ofPieces_single {x : Inst} {τ : Sched x} {j : Fin x.jobs} {q : Piece x}
    (h : piecesOf τ j = [q]) (n : ℕ) (hn : q.start = (n : NNRat)) :
    (ofPieces x τ).machines j = q.machines ∧ ((ofPieces x τ).start j : NNRat) = q.start := by
  refine ⟨by simp [ofPieces, h], ?_⟩
  have hs : ((piecesOf τ j).head?).map Piece.start = some ((Classical.epsilon fun n : ℕ =>
      ((piecesOf τ j).head?).map Piece.start = some (n : NNRat) : ℕ) : NNRat) :=
    Classical.epsilon_spec (p := fun n : ℕ =>
      ((piecesOf τ j).head?).map Piece.start = some (n : NNRat)) ⟨n, by simp [h, hn]⟩
  change ((Classical.epsilon fun n : ℕ =>
      ((piecesOf τ j).head?).map Piece.start = some (n : NNRat) : ℕ) : NNRat) = q.start
  generalize (Classical.epsilon fun n : ℕ =>
      ((piecesOf τ j).head?).map Piece.start = some (n : NNRat)) = e at hs ⊢
  rw [h] at hs
  exact (Option.some.inj hs).symm

theorem ofPieces_back {x : Inst} (τ : Sched x) (hf : Interruption.feasible τ)
    (hm : Interruption.Mode.none.holds x τ) :
    Nonpreemptive.feasible x (ofPieces x τ) ∧ Agree pieces nonpreemptiveSys x τ (ofPieces x τ) := by
  have key : ∀ j, ∃ q, piecesOf τ j = [q] ∧ (ofPieces x τ).machines j = q.machines ∧
      ((ofPieces x τ).start j : NNRat) = q.start ∧
      (Nonpreemptive.completion x (ofPieces x τ) j : NNRat) = q.finish := by
    intro j
    obtain ⟨q, hq, hl, n, hn⟩ := hm j
    obtain ⟨h1, h2⟩ := ofPieces_single hq n hn
    refine ⟨q, hq, h1, h2, ?_⟩
    unfold Nonpreemptive.completion
    push_cast
    rw [h2, h1, Piece.finish, hl]
  have mem : ∀ j q, piecesOf τ j = [q] → q ∈ τ.pieces ∧ q.job = j := fun j q h =>
    mem_piecesOf.mp (h ▸ List.mem_singleton_self q)
  refine ⟨⟨fun j => ?_, fun i j hij hd => ?_⟩, fun j => ?_, fun j => ?_, fun j S hS => ?_⟩
  · obtain ⟨q, hq, h1, -⟩ := key j
    rw [h1]
    exact hf.1 q (mem j q hq).1
  · obtain ⟨qi, hqi, hi1, hi2, hi3⟩ := key i
    obtain ⟨qj, hqj, hj1, hj2, hj3⟩ := key j
    have hmi := mem i qi hqi
    have hmj := mem j qj hqj
    have hne : qi ≠ qj := fun h => hij (hmi.2.symm.trans (h ▸ hmj.2))
    rw [hi1, hj1] at hd
    rcases apart_of_feasible hf.2 hmi.1 hmj.1 hne (Or.inl hd) with h | h
    · left
      have : (Nonpreemptive.completion x (ofPieces x τ) i : NNRat) ≤ ((ofPieces x τ).start j : NNRat) := by
        rw [hi3, hj2]
        exact h
      exact_mod_cast this
    · right
      have : (Nonpreemptive.completion x (ofPieces x τ) j : NNRat) ≤ ((ofPieces x τ).start i : NNRat) := by
        rw [hj3, hi2]
        exact h
      exact_mod_cast this
  · obtain ⟨q, hq, -, h2, -⟩ := key j
    change ((ofPieces x τ).start j : NNRat) = start x τ j
    rw [h2, start_single hq]
  · obtain ⟨q, hq, -, -, h3⟩ := key j
    change (Nonpreemptive.completion x (ofPieces x τ) j : NNRat) = completion x τ j
    rw [h3, completion_single hq]
  · obtain ⟨q, hq, h1, -⟩ := key j
    exact ⟨q, hq ▸ List.mem_singleton_self q, h1 ▸ hS⟩

/-- The non-preemptive embedding is sound. -/
theorem nonpreemptive_sound (s : Spec ParallelProblems.nonpreemptive) :
    (⟨toNew nonpreemptiveSys .none, fun x σ => toPieces x.base σ, fun x τ => ofPieces x.base τ⟩ :
      Embedding (problem _ s) (problem family (ofSpec .none s))).Sound :=
  toNew_sound (P := nonpreemptiveSys) s toPieces ofPieces
    (fun _ σ hf => toPieces_forth σ hf) (fun _ τ hf hm => ofPieces_back τ hf hm)

/--
---
conclusion: Lax434175.ParallelFamily.nonpreemptive_faithful
---
A non-preemptive schedule is a schedule with one full piece per job starting
at an integral time.
-/
theorem nonpreemptive_faithful (s : Spec ParallelProblems.nonpreemptive) :
    SpecialCase (problem _ s) (problem family (ofSpec .none s)) ∧
      SpecialCase (problem family (ofSpec .none s)) (problem _ s) :=
  faithful (P := nonpreemptiveSys) s toPieces ofPieces
    (fun _ σ hf => toPieces_forth σ hf) (fun _ τ hf hm => ofPieces_back τ hf hm)

end Nonpreemptive

/--
---
conclusion: Lax434175.ParallelFamily.family_sound
---
-/
theorem family_sound : family.Sound where
  module
    | .interruption => Interruption.sound
    | .field i => (ParallelProblems.family_sound Interruption.model).module i
  objective := Objectives.sound _

/--
---
conclusion: Lax434175.ParallelFamily.specialCase_of_le
---
-/
theorem specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t) :=
  fun h => ⟨lift family family_sound h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.ParallelFamily.reducible_of_reduces
---
-/
theorem reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t) :=
  Thresholds.reducible_of_reduces family_sound.module

/--
---
conclusion: Lax434175.ParallelFamily.reducible_of_reducesThroughFlow
---
A job starts no earlier than its release date and completes no earlier than
it starts.
-/
theorem reducible_of_reducesThroughFlow {s t : Spec family} :
    Thresholds.ReducesThroughFlow s t → Reducible (problem family s) (problem family t) :=
  Thresholds.reducible_of_reducesThroughFlow family_sound.module
    (fun _ x _ σ _ hf hc j => le_trans (hc (.field .releaseDates) j)
      (Interruption.startsBeforeCompletion x σ hf j))

end Lax434175Proofs.ParallelFamily
