import Mathlib.Tactic
import Lax434175Proofs.IsemBridge
import Lax434175Proofs.IsemClamp
import Lax434175.IsemStrong

/-!
`P|M_j|Σ w_j Z_j` is strongly W[1]-hard for the number of machines. The chain of
`IsemBridge` (Construction 1 of lax-888481, padding, the standard word), with the threshold
lowered to at most the total weight plus one before the standard word is written, lands in the
words whose numbers are at most `2^31 (ℓ + 1)^31` for `ℓ` their length. With `n ≥ 1` vertices
every number is at most `(n + k + 2)^31`, and the word has a record for each of the at least
`n + k` jobs; with no vertex the instance has no job and, after the threshold is lowered, all
its numbers are at most `40`.
-/

namespace Lax434175Proofs.IsemStrong
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.IsemLink
open Lax434175.ResultParameters
open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175Proofs.IsemWords Lax434175Proofs.IsemCompress Lax434175Proofs.IsemClamp
open Lax434175Proofs.IsemBridge Lax434175Proofs.PadWord
open Lax434175Proofs.JitHardness (base1 mulB monoB addB oneB)
open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

/-! ### Lengths and numbers along the chain -/

theorem foldr_max_le {M : ℕ} : ∀ {l : List ℕ}, (∀ v ∈ l, v ≤ M) → l.foldr max 0 ≤ M
  | [], _ => Nat.zero_le _
  | a :: t, h => by
      simp only [List.foldr_cons]
      exact max_le (h a List.mem_cons_self) (foldr_max_le fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem capN_append {y : List ℕ} {I : Instance} (h : EncodesInstance y I) (W : ℕ) :
    capN (y ++ [W]) = I.jobs := by
  have hlen := h.length_eq
  have hjc : jobCount (y ++ [W]) = I.jobs := by
    unfold jobCount; rw [getD_append_left (by omega)]; exact h.jobCount_eq
  unfold capN; rw [hjc]; simp; omega

theorem length_flatMap_range (f : ℕ → List ℕ) (hf : ∀ j, f j ≠ []) :
    ∀ m, m ≤ ((List.range m).flatMap f).length
  | 0 => Nat.zero_le _
  | m + 1 => by
      rw [List.range_succ, List.flatMap_append, List.length_append]
      have := length_flatMap_range f hf m
      have : 0 < ((([m] : List ℕ)).flatMap f).length := by
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact List.length_pos_of_ne_nil (hf m)
      omega

theorem capN_le_std (y : List ℕ) : capN y ≤ (stdOfWord y).length := by
  have h := length_flatMap_range (fun j => (recW y (capM y) j).length :: recW y (capM y) j)
    (fun _ => List.cons_ne_nil _ _) (capN y)
  unfold stdOfWord
  simp only [List.length_append] at h ⊢
  omega

theorem length_compressWord (u : List ℕ) : (compressWord u).length ≤ 5 * u.length + 4 := by
  have hn : capN u ≤ u.length := min_le_right _ _
  have hT : min (offset u (capN u)) u.length ≤ u.length := min_le_right _ _
  unfold compressWord
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  omega

/-! ### The numbers of Construction 1 -/

section Construction1
open Lax888481.MulticolouredClique Lax888481.Construction1

variable (G : Lax888481.MulticolouredClique.Instance)

theorem length_emit : (emit G).length ≤ 6 * nJobs G + 4 := by
  have ht : (tgtBlock G).length ≤ 2 * nJobs G := by
    unfold tgtBlock
    rw [List.length_flatMap]
    have := List.sum_le_card_nsmul ((List.range (nJobs G)).map fun i => (eligOf G i).length) 2
      (by intro a ha; obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
          exact Lax434175Proofs.JitHardness.elig_length G i)
    simpa [mul_comm] using this
  unfold emit procBlock dueBlock wtBlock offBlock
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  omega

theorem nJobs_ge (hn : 1 ≤ G.vertices) : G.vertices + G.colours ≤ nJobs G := by
  have hk : 1 ≤ G.colours := by
    have := (G.colour ⟨0, hn⟩).isLt
    omega
  unfold nJobs nVJob nCJob
  have h1 : G.vertices ≤ G.vertices * G.colours := Nat.le_mul_of_pos_right _ hk
  have h2 : G.colours ≤ G.colours * G.colours * G.vertices := by
    calc G.colours ≤ G.colours * G.colours := Nat.le_mul_of_pos_right _ hk
      _ ≤ G.colours * G.colours * G.vertices := Nat.le_mul_of_pos_right _ hn
  omega

theorem nJobs_zero (hn : G.vertices = 0) : nJobs G = 0 := by
  have he : edgeList G = [] := by
    unfold edgeList
    have : List.finRange G.vertices = [] := by rw [List.finRange_eq_nil_iff]; exact hn
    rw [this]; rfl
  unfold nJobs nVJob nCJob nEJob
  rw [he, hn]; simp

theorem emit_zero (hn : G.vertices = 0) : emit G = [0, nMach G, 0, targetWeight G] := by
  have h0 := nJobs_zero G hn
  unfold emit procBlock dueBlock wtBlock offBlock tgtBlock
  rw [h0]
  simp [offOf]

end Construction1

/-! ### The final map -/

/-- The word map from interval scheduling: lower the threshold, then the map of `IsemBridge`. -/
def fin (x : List ℕ) : List ℕ := isemToStd (clampW x)

/-- The chain from a word of Multicoloured Clique: Construction 1, padding, the final map. -/
noncomputable def chain (x : List ℕ) : List ℕ := fin (padWord (Lax888481.Construction1.reduce x))

/-- With no vertex, the numbers of the chain are at most `40`. -/
theorem chain_zero (G : Lax888481.MulticolouredClique.Instance) (hn : G.vertices = 0) :
    ∀ v ∈ fin (padWord (Lax888481.Construction1.emit G)), v ≤ 40 := by
  rw [emit_zero G hn]
  set m := Lax888481.Construction1.nMach G
  set T := Lax888481.Construction1.targetWeight G
  have hp : padWord [0, m, 0, T] = [0, m + 1, 0, T] := by
    simp [padWord, padInst, P, Dl, Wt, O, PadWord.T, os, nOf, jobCount, machineCount,
      Lax434175Proofs.PadProgram.empties]
  have hc : clampW [0, m + 1, 0, T] = [0, m + 1, 0, min T 1] := by
    simp [clampW, lastOf, totalW, capN, jobCount]
  have hw : compressWord [0, m + 1, 0, min T 1] = [0, 0, 0, min T 1] := by
    simp [compressWord, capN, jobCount, offset, lastOf, firsts]
  unfold fin isemToStd
  rw [hp, hc, hw]
  intro v hv
  have h := Lax434175Proofs.IsemPrograms.stdOfWord_le _ v hv
  have hM : maxEntry [0, 0, 0, min T 1] ≤ 1 :=
    foldr_max_le fun u hu => by simp at hu; rcases hu with rfl | rfl <;> omega
  simp only [List.length_cons, List.length_nil] at h
  have : 4 * maxEntry [0, 0, 0, min T 1] ≤ 4 := by omega
  omega

/-- `2 A^15 + 1`, `6 A^5 + 4` and the rest, against powers of `A ≥ 2`. -/
theorem arith {A L0 L1 M1 L3 M3 v : ℕ} (hA : 2 ≤ A) (hL0 : L0 ≤ A ^ 8) (hL1 : L1 ≤ 2 * L0)
    (hM1 : M1 ≤ 2 * A ^ 15 + 1) (hM3 : M3 ≤ L1 + M1) (hL3 : L3 ≤ 5 * L1 + 4)
    (hv : v ≤ L3 * M3 + 4 * (L3 + M3 + 4)) : v ≤ A ^ 31 := by
  have h2 : 2 ≤ A ^ 1 := by rw [pow_one]; exact hA
  have h4 : 4 ≤ A ^ 2 := by nlinarith
  have hL1' : L1 ≤ A ^ 9 := by
    have := mulB h2 hL0; rw [show 1 + 8 = 9 by rfl] at this; omega
  have hM1' : M1 ≤ A ^ 17 := by
    have h := mulB h4 (le_refl (A ^ 15))
    have : 1 ≤ A ^ 15 := oneB (by omega) 15
    rw [show 2 + 15 = 17 by rfl] at h; omega
  have hM3' : M3 ≤ A ^ 18 := hM3.trans (addB hA hL1' hM1' (by omega) (by omega))
  have hL3' : L3 ≤ A ^ 12 := by
    have h8 : 8 ≤ A ^ 3 := by
      have := mulB h2 h4; rw [show 1 + 2 = 3 by rfl] at this; omega
    have h := mulB h8 (le_refl (A ^ 9))
    have : 2 ≤ A ^ 9 := (show 2 ≤ A ^ 1 by rw [pow_one]; exact hA).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
    rw [show 3 + 9 = 12 by rfl] at h; omega
  have hp : L3 * M3 ≤ A ^ 30 := mulB hL3' hM3'
  have hq : 4 * (L3 + M3 + 4) ≤ A ^ 30 := by
    have a1 : 4 * L3 ≤ A ^ 14 := by have := mulB h4 hL3'; rwa [show 2 + 12 = 14 by rfl] at this
    have a2 : 4 * M3 ≤ A ^ 20 := by have := mulB h4 hM3'; rwa [show 2 + 18 = 20 by rfl] at this
    have a3 : 16 ≤ A ^ 4 := by have := mulB h4 h4; rwa [show 2 + 2 = 4 by rfl] at this
    have := addB (c := 22) hA (addB (c := 21) hA a1 a2 (by omega) (by omega)) a3 (by omega) (by omega)
    have := monoB (by omega) this (show 22 ≤ 30 by omega)
    omega
  have h31 : A ^ 31 = A * A ^ 30 := by rw [pow_succ, mul_comm]
  have : 2 * A ^ 30 ≤ A * A ^ 30 := Nat.mul_le_mul_right _ hA
  omega

/-- With a vertex, the numbers of the chain are at most `2^31 (ℓ + 1)^31`. -/
theorem chain_pos (G : Lax888481.MulticolouredClique.Instance) (hn : 1 ≤ G.vertices) :
    fin (padWord (Lax888481.Construction1.emit G)) ∈ Small (2 ^ 31) 31 := by
  obtain ⟨y0, he, hy0⟩ := Lax888481.Construction1.emit_encodes G
  set I := Lax888481.Construction1.inst G
  set T := Lax888481.Construction1.targetWeight G
  set A := base1 G
  have hA : 2 ≤ A := Lax434175Proofs.JitHardness.two_le G
  set J := Lax888481.Construction1.nJobs G
  have hJ : I.jobs = J := rfl
  have hy1 := Lax434175Proofs.PadEncoding.encodes_pad hy0
  set W' := min T (totalWeight (pad I) + 1)
  have hu1 : padWord (Lax888481.Construction1.emit G) = padInst y0 ++ [T] := by
    rw [he, padWord_append]
  have hu2 : clampW (padInst y0 ++ [T]) = padInst y0 ++ [W'] := clampW_append hy1 T
  obtain ⟨y1, hu3, hy1', -⟩ := compressWord_eq (W := W') hy1
  -- the words
  set u0 := Lax888481.Construction1.emit G
  set u1 := padInst y0 ++ [T]
  set u2 := padInst y0 ++ [W']
  set u3 := compressWord u2
  have hw : fin (padWord u0) = stdOfWord u3 := by
    unfold fin isemToStd; rw [hu1, hu2]
  -- lengths
  have hL0 : u0.length ≤ A ^ 8 := by
    have h1 := length_emit G
    have h2 : J ≤ A ^ 5 := Lax434175Proofs.JitHardness.nJobs_le G
    have h3 : 2 ≤ A ^ 5 := (show 2 ≤ A ^ 1 by rw [pow_one]; exact hA).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
    have h8 : 8 ≤ A ^ 3 := by
      have : 2 ^ 3 ≤ A ^ 3 := Nat.pow_le_pow_left hA 3
      simpa using this
    have h5 : 8 * A ^ 5 ≤ A ^ 3 * A ^ 5 := Nat.mul_le_mul_right _ h8
    rw [← pow_add, show 3 + 5 = 8 by rfl] at h5
    show (Lax888481.Construction1.emit G).length ≤ A ^ 8
    omega
  have hjc : jobCount y0 = J := hy0.jobCount_eq
  have hL1 : u1.length ≤ 2 * u0.length := by
    have e1 := hy1.length_eq
    have e0 := hy0.length_eq
    have hp := Lax434175Proofs.PadEncoding.offset_pad hy0 (j := J) (by show J ≤ jobCount y0; omega)
    have ho : os y0 J = offset y0 J := (offset_eq y0 (by show J ≤ jobCount y0; omega)).symm
    have hemp := Lax434175Proofs.PadReduction.empties_le (os y0) J
    have hpj : (pad I).jobs = J := rfl
    rw [hpj] at e1
    rw [hJ] at e0
    have hu0 : u0.length = y0.length + 1 := by
      have := congrArg List.length he
      simpa using this
    show (padInst y0 ++ [T]).length ≤ _
    simp only [List.length_append, List.length_singleton]
    omega
  have hM0 : u0.foldr max 0 ≤ A ^ 15 := foldr_max_le fun v hv => Lax434175Proofs.JitHardness.emit_le G hv
  have hM1 : maxEntry u1 ≤ 2 * A ^ 15 + 1 := foldr_max_le fun v hv => by
    have := Lax434175Proofs.PadReduction.padWord_le u0 v (by rw [hu1]; exact hv)
    omega
  have hM2 : maxEntry u2 ≤ 2 * A ^ 15 + 1 := foldr_max_le fun v hv => by
    rw [← hu2] at hv
    exact (clampW_le _ v hv).trans hM1
  have hL2 : u2.length = u1.length := by simp [u1, u2]
  have hM3 : maxEntry u3 ≤ u1.length + (2 * A ^ 15 + 1) := foldr_max_le fun v hv => by
    have := Lax434175Proofs.IsemPrograms.compressWord_le u2 v hv
    omega
  have hL3 : u3.length ≤ 5 * u1.length + 4 := hL2 ▸ length_compressWord u2
  -- the length of the standard word
  have hlen : G.vertices + G.colours ≤ (stdOfWord u3).length := by
    have h1 := capN_le_std u3
    rw [show u3 = y1 ++ [W'] from hu3, capN_append hy1'] at h1
    have h2 := nJobs_ge G hn
    have : (compress (pad I)).jobs = J := rfl
    rw [show u3 = y1 ++ [W'] from hu3]
    omega
  rw [hw]
  intro v hv
  have hv' := Lax434175Proofs.IsemPrograms.stdOfWord_le u3 v hv
  have hvA : v ≤ A ^ 31 := arith hA hL0 hL1 (le_refl _) hM3 hL3
    (hv'.trans (by
      have := Nat.mul_le_mul hL3 hM3
      have hmax := hM3
      nlinarith))
  have hAl : A ≤ 2 * ((stdOfWord u3).length + 1) := by
    show G.vertices + G.colours + 2 ≤ _; omega
  calc v ≤ A ^ 31 := hvA
    _ ≤ (2 * ((stdOfWord u3).length + 1)) ^ 31 := Nat.pow_le_pow_left hAl 31
    _ = 2 ^ 31 * ((stdOfWord u3).length + 1) ^ 31 := by rw [mul_pow]

/-! ### The reductions onto the words with small numbers -/

/-- The zoo's problem on its standard words, parameterized by the number of machines. -/
noncomputable abbrev Tgt : Lax888481.ParameterizedComplexity.Problem :=
  parameterized (StandardReading.ops.at ZooParallel.p200) (lift (Ops.m ZooParallel.p200))

/-- The words of interval scheduling whose final word has small numbers. -/
def S2 : Set (List ℕ) := {x | fin x ∈ Small (2 ^ 31) 31}

/-- The words of interval scheduling whose padding is in `S2`. -/
def S1 : Set (List ℕ) := {y | padWord y ∈ S2}

theorem reduce_mem {x : List ℕ} (hx : x ∈ Lax888481.MulticolouredClique.problem.Domain) :
    Lax888481.Construction1.reduce x ∈ S1 := by
  have hx' : ∃ G, Lax888481.MulticolouredClique.EncodesInstance x G := hx
  show fin (padWord (Lax888481.Construction1.reduce x)) ∈ Small (2 ^ 31) 31
  unfold Lax888481.Construction1.reduce
  rw [dif_pos hx']
  set G := hx'.choose
  by_cases hn : G.vertices = 0
  · intro v hv
    have h1 := chain_zero G hn v hv
    have h2 : 1 ≤ ((fin (padWord (Lax888481.Construction1.emit G))).length + 1) ^ 31 :=
      Nat.one_le_pow _ _ (by omega)
    have h3 : 40 ≤ 2 ^ 31 := by norm_num
    nlinarith
  · exact chain_pos G (by omega)

section Strict
open Lax888481.ParameterizedComplexity (IsFptReduction)

theorem restrictTgt {P Q : Lax888481.ParameterizedComplexity.Problem} {f : List ℕ → List ℕ} {prog : Lax808846.Ram.Program} {c : ℕ}
    {g h : ℕ → ℕ} (hr : IsFptReduction P Q f prog c g h) (D : Set (List ℕ))
    (hD : ∀ x ∈ P.Domain, f x ∈ D) : IsFptReduction P (restrict Q D) f prog c g h where
  maps_domain x hx := ⟨hr.maps_domain x hx, hD x hx⟩
  correct x hx := hr.correct x hx
  param_le x hx := hr.param_le x hx
  time := hr.time

theorem restrictSrc {P Q : Lax888481.ParameterizedComplexity.Problem} {f : List ℕ → List ℕ} {prog : Lax808846.Ram.Program} {c : ℕ}
    {g h : ℕ → ℕ} (hr : IsFptReduction P Q f prog c g h) (E : Set (List ℕ)) :
    IsFptReduction (restrict P E) Q f prog c g h where
  maps_domain x hx := hr.maps_domain x hx.1
  correct x hx := hr.correct x hx.1
  param_le x hx := hr.param_le x hx.1
  time w x hx := hr.time w x ⟨hx.1.1, hx.2⟩

end Strict

open Lax808846.Ram Lax759944.BinaryWordEncoding in
/-- Construction 1 of lax-888481, onto the words in `S1`. -/
theorem mcc_le :
    Lax888481.MulticolouredClique.problem ≤ᶠᵖᵗ restrict Lax888481.SchedulingProblems.byMachines S1 := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_strict
    (restrictTgt Lax434175Proofs.JitHardness.construction1 S1 fun x hx => reduce_mem hx)
    Lax434175Proofs.JitHardness.computable_gOf Lax434175Proofs.JitHardness.computable_sq
    ⟨fun k => 15 * (k + 2), 1,
      (Primrec.nat_mul.comp (Primrec.const 15) (Primrec.succ.comp Primrec.succ)).to_comp, ?_⟩
  rintro x ⟨G, hG⟩ v hv
  have hx : ∃ G, Lax888481.MulticolouredClique.EncodesInstance x G := ⟨G, hG⟩
  unfold Lax888481.Construction1.reduce at hv
  rw [dif_pos hx] at hv
  have hG' := hx.choose_spec
  set G' := hx.choose
  obtain ⟨g, hxg, -⟩ := hG'
  have hn : G'.vertices ≤ bitSize x := by
    have := Lax496464.WH_A4_MachineFacts.length_le_bitSize x
    have hl : G'.vertices ≤ x.length := by rw [hxg]; simp; omega
    omega
  have hk : Lax888481.MulticolouredClique.problem.param x = G'.colours := by
    show (x.getLast?.getD 0) = _
    rw [hxg]; simp
  rw [hk]
  show v < 2 ^ (15 * (G'.colours + 2) * (bitSize x + 1) ^ 1)
  rw [pow_one, mul_assoc]
  refine Lax434175Proofs.JitHardness.lt_pow_of_le_pow (Lax434175Proofs.JitHardness.emit_le G' hv) ?_
  unfold base1
  nlinarith

open Lax759944.BinaryWordEncoding in
/-- Padding, from `S1` onto `S2`. -/
theorem pad_le : restrict Lax888481.SchedulingProblems.byMachines S1 ≤ᶠᵖᵗ restrict jitByMachines S2 := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_strict
    (restrictTgt (restrictSrc Lax434175Proofs.PadReduction.isFptReduction S1) S2 fun _ hx => hx.2)
    (Computable.const 1) Computable.succ ⟨fun _ => 1, 1, Computable.const 1, ?_⟩
  intro x _ v hv
  have h := Lax434175Proofs.PadReduction.padWord_le x v hv
  have hM : x.foldr max 0 < 2 ^ bitSize x := by
    rcases Lax434175Proofs.PadReduction.foldr_max_mem_or_zero x with hm | hm
    · exact Lax496464.WH_A4_MachineFacts.lt_two_pow_bitSize hm
    · rw [hm]; exact Nat.two_pow_pos _
  rw [one_mul, pow_one, pow_succ]
  omega

open Lax759944.BinaryWordEncoding in
theorem fin_turing : Nonempty (Turing.TM2ComputableInPolyTime encode encode fin) := by
  obtain ⟨t1⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    clampW_polytime
  obtain ⟨t2⟩ := isemToStd_turing
  exact Lax888481Proofs.TMCompose.comp t1 t2

/-- The final map, from `S2` onto the standard words with small numbers. -/
theorem fin_le : restrict jitByMachines S2 ≤ᶠᵖᵗ restrict Tgt (Small (2 ^ 31) 31) := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_polyTime (R := fin)
    ⟨fun x hx => ?_, fun x hx => ?_⟩ ⟨id, Computable.id, fun x hx => ?_⟩
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_turingPolytime _ fin_turing)
  · obtain ⟨⟨I, W, hx, -⟩, hs⟩ := hx
    exact ⟨⟨_, _, isemToStd_encodes (clampW_encodes hx)⟩, hs⟩
  · obtain ⟨⟨I, W, hx, hI⟩, -⟩ := hx
    show (∃ I' W', EncodesDecisionInstance x I' W' ∧ _) ↔ (decision _).Yes (fin x)
    rw [fin, yes_isemToStd (clampW_encodes hx) hI, hasWeight_min]
    constructor
    · rintro ⟨I', W', hx', h⟩
      obtain ⟨rfl, rfl⟩ := Lax434175Proofs.IsemLink.encodesDecision_unique hx hx'
      exact (hasWeight_iff I hI W).mpr h
    · exact fun h => ⟨I, W, hx, (hasWeight_iff I hI W).mp h⟩
  · classical
    obtain ⟨⟨I, W, hx, -⟩, -⟩ := hx
    have henc := isemToStd_encodes (clampW_encodes hx)
    show (if h : ∃ y D, EncodesDecision (StandardReading.ops.at ZooParallel.p200) (fin x) y D then
      lift (Ops.m ZooParallel.p200) h.choose h.choose_spec.choose else 0) ≤ machineCount x
    split_ifs with h
    · have hb := Lax434175.PropagationParameters.ops_m p200_le rfl rfl (fin x) _ _ _ _ henc
        h.choose_spec.choose_spec
      obtain ⟨y0, rfl, hy0⟩ := hx
      rw [machineCount_eq hy0]
      exact hb.le.trans m_le
    · exact Nat.zero_le _

/--
---
conclusion: Lax434175.IsemStrong.p200_r0_holds
---
Construction 1 of lax-888481, padding, the threshold lowered to the total weight plus one, and
the standard word: Multicoloured Clique fpt-reduces to the words whose numbers are at most
`2^31 (ℓ + 1)^31`.
-/
theorem p200_r0_holds : ZooParallelResults.p200_r0 StandardReading.ops :=
  ⟨2 ^ 31, 31, Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces
    Lax496464.WH_D12_MulticolouredClique.multicolouredClique_W1_complete.2
    (Lax496464.WH_A3_ReductionCalculus.fptReduces_trans mcc_le
      (Lax496464.WH_A3_ReductionCalculus.fptReduces_trans pad_le fin_le))⟩

end Lax434175Proofs.IsemStrong
