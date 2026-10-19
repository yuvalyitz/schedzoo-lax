import Mathlib.Tactic
import Lax434175Proofs.JitFlowShop
import Lax434175Proofs.IsemStandard
import Lax434175.StandardReading

/-!
The standard word of the zoo instance `toZooUnit J` of a flow shop instance `J` of lax-496464:
for every job its record (two operations, the times of each on all `m + 1` machines, the
machine tuples of the stages, no server, the four zero transport delays), then the empty block of
pairs, the global block of the batch setup, and the release dates, unit weights and due dates.
-/

namespace Lax434175Proofs.JitWords
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.JitFlowShop
open Lax434175.StandardReading Lax434175.ResultParameters
open Lax496464.FlowShop
open Lax434175Proofs.IsemStandard (block_empty block_single machinesWord_singleton)

/-- The machine tuples of a job: `[0, 0]` for the first operation, `[1, i]` for the second one
on machine `i ≥ 1`. -/
def machList (M : ℕ) : List (List ℕ) := [0, 0] :: (List.range M).map fun i => [1, i + 1]

/-- The transport tuples of a job: all four delays `0`. -/
def transList : List (List ℕ) := [[0, 0, 0], [0, 1, 0], [1, 0, 0], [1, 1, 0]]

/-- The record of a job with operations of lengths `p` and `q`, among `M + 1` machines. -/
def recJ (M p q : ℕ) : List ℕ :=
  [2] ++ List.replicate (M + 1) p ++ List.replicate (M + 1) q ++ [0] ++ flat (machList M) ++
    [0] ++ flat transList ++ [0]

/-- The global block: the batch setup `[1, 0, 0, 0]` when there are jobs. -/
def globJ (n : ℕ) : List ℕ := if n = 0 then [0] else [1, 4, 1, 0, 0, 0]

/-- The standard word of `toZooUnit J`. -/
def stdJ (J : Instance) : List ℕ :=
  [0, J.jobs, J.machines + 1] ++
    (List.ofFn fun t => (recJ J.machines (J.p t) (J.q t)).length ::
      recJ J.machines (J.p t) (J.q t)).flatten ++ [0] ++ globJ J.jobs ++
    (List.ofFn fun t => [0, 1, J.d t]).flatten

variable (J : Instance)

theorem lt_one_cons {a b : ℕ} (h : a < b) : ([1, a] : List ℕ) < [1, b] :=
  List.Lex.cons (List.Lex.rel h)

theorem machList_lists (j : Fin J.jobs) :
    Lists (machineTuples (toZooUnit J) j) (machList J.machines) := by
  refine ⟨?_, fun t => ?_⟩
  · unfold machList
    refine List.Pairwise.cons (fun b hb => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      exact List.Lex.rel (by norm_num)
    · exact List.Pairwise.map _ (fun a b h => lt_one_cons (by omega)) List.pairwise_lt_range
  · unfold machList machineTuples
    simp only [List.mem_cons, List.mem_map, List.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · refine ⟨(0 : Fin 2), Shops.machineNumbered (base J).toShop 0, ⟨fun _ => rfl, fun h => absurd rfl h⟩, ?_⟩
        have : Shops.machineNumbered (base J).toShop 0 = {⟨0, Nat.succ_pos _⟩} := by
          ext a; simp [Shops.machineNumbered, Fin.ext_iff]
        rw [this]
        exact congrArg (List.cons 0)
          (machinesWord_singleton (m := (toZooUnit J).base.machines) ⟨0, Nat.succ_pos _⟩).symm
      · refine ⟨(1 : Fin 2), {⟨i + 1, by show i + 1 < J.machines + 1; omega⟩},
          ⟨fun h => absurd h one_ne_zero, fun _ => ⟨Finset.card_singleton _, fun a ha => ?_⟩⟩, ?_⟩
        · rw [Finset.mem_singleton.mp ha]; simp
        · simp [machinesWord]
    · rintro ⟨k, S, ⟨h0, h1⟩, rfl⟩
      rcases Fin.exists_fin_two.mp ⟨k, rfl⟩ with rfl | rfl
      · left
        have hS := h0 rfl
        have : S = {⟨0, Nat.succ_pos _⟩} := by
          rw [hS]; ext a; simp [Shops.machineNumbered, Fin.ext_iff]
        rw [this]; simp [machinesWord]
      · right
        obtain ⟨hc, hne⟩ := h1 one_ne_zero
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        have ha := hne a (Finset.mem_singleton_self _)
        refine ⟨a.val - 1, by have := a.isLt; change a.val < J.machines + 1 at this; omega, ?_⟩
        simp only [machinesWord, Finset.image_singleton, Finset.sort_singleton]
        show [1, a.val - 1 + 1] = [1, a.val]
        congr 2; omega

theorem transList_lists (j : Fin J.jobs) : Lists (transportTuples (toZooUnit J) j) transList := by
  refine ⟨by decide, fun t => ?_⟩
  unfold transList transportTuples
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨(0 : Fin 2), (0 : Fin 2), rfl⟩
    · exact ⟨(0 : Fin 2), (1 : Fin 2), rfl⟩
    · exact ⟨(1 : Fin 2), (0 : Fin 2), rfl⟩
    · exact ⟨(1 : Fin 2), (1 : Fin 2), rfl⟩
  · rintro ⟨k, k', rfl⟩
    rcases Fin.exists_fin_two.mp ⟨k, rfl⟩ with rfl | rfl <;>
      rcases Fin.exists_fin_two.mp ⟨k', rfl⟩ with rfl | rfl <;> simp <;> rfl

theorem server_empty (j : Fin J.jobs) : serverTuples (toZooUnit J) j = ∅ := by
  ext t
  simp only [serverTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, f, hf, -⟩
  cases hf

theorem jobHead_eq (j : Fin J.jobs) :
    jobHead (toZooUnit J) j = [2] ++ List.replicate (J.machines + 1) (J.p j) ++
      List.replicate (J.machines + 1) (J.q j) ++ [0] := by
  show [2] ++ (List.ofFn fun k : Fin 2 => List.ofFn fun _ : Fin (J.machines + 1) =>
    if k.val = 0 then J.p j else J.q j).flatten ++ enat ⊤ = _
  simp [enat, List.ofFn_const, List.ofFn_succ, List.replicate_succ]

theorem record (j : Fin J.jobs) :
    Record (toZooUnit J) j (recJ J.machines (J.p j) (J.q j)) := by
  refine ⟨flat (machList J.machines), [0], flat transList, ⟨_, machList_lists J j, rfl⟩,
    server_empty J j ▸ block_empty, ⟨_, transList_lists J j, rfl⟩, ?_⟩
  rw [jobHead_eq]
  rfl

theorem pair_empty : pairTuples (toZooUnit J) = ∅ := by
  ext t
  simp only [pairTuples, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ((⟨i, j, h, -⟩ | ⟨i, j, h, -⟩) | ⟨i, j, c, h, -⟩) <;> exact h

theorem global_eq : globalTuples (toZooUnit J) = if J.jobs = 0 then ∅ else {[1, 0, 0, 0]} := by
  ext t
  simp only [globalTuples, Set.mem_union, Set.mem_ofPred_eq]
  split_ifs with hn
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ((⟨τ, hτ, -⟩ | ⟨i, -, -⟩) | ⟨hr, -⟩)
    · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
    · exact absurd i.isLt (by have h : (toZooUnit J).base.jobs = J.jobs := rfl; omega)
    · exact absurd hr (by decide)
  · simp only [Set.mem_singleton_iff]
    constructor
    · rintro ((⟨τ, hτ, -⟩ | ⟨i, j, rfl⟩) | ⟨hr, -⟩)
      · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
      · rfl
      · exact absurd hr (by decide)
    · rintro rfl
      have hp : 0 < (toZooUnit J).base.jobs := by
        have h : (toZooUnit J).base.jobs = J.jobs := rfl; omega
      exact Or.inl (Or.inr ⟨⟨0, hp⟩, ⟨0, hp⟩, rfl⟩)

theorem global_block : Block (globalTuples (toZooUnit J)) (globJ J.jobs) := by
  rw [global_eq]
  unfold globJ
  split_ifs
  · exact block_empty
  · exact block_single _

/-- **The standard word of `toZooUnit J`.** -/
theorem encodesOps : EncodesOps (toZooUnit J) (stdJ J) :=
  ⟨[0], _, pair_empty J ▸ block_empty, global_block J,
    Or.inl ⟨rfl, _, ⟨fun j => recJ J.machines (J.p j) (J.q j), record J, rfl⟩, rfl⟩⟩

/-- The standard word with a threshold. -/
def stdWordJ (D : ℤ) : List ℕ := stdJ J ++ [if D < 0 then 1 else 0, D.natAbs]

theorem encodesDecision (D : ℤ) :
    Lax434175.Results.EncodesDecision (StandardReading.ops.at ZooShops.p315) (stdWordJ J D)
      (toZooUnit J) D :=
  ⟨stdJ J, rfl, encodesOps J⟩

end Lax434175Proofs.JitWords
