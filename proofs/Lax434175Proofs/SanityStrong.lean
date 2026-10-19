import Mathlib.Tactic
import Lax434175.SanityParams
import Lax429075.SATHard
import Lax391470.Theorem1
import Lax434175Proofs.Sanity
import Lax434175Proofs.ThresholdWords

/-!
`1|r_j|L_max` is strongly NP-hard on the standard reading.

The reduction of `Sanity.npHard_rjLmax` with the existential reduction of lax-391470 replaced
by its explicit maps: Cook–Levin (lax-429075) to satisfiability, then `Lemma2.reduce 3 2` to the
auxiliary problem, then `Lemma1.reduce 3 2` to scheduling on the lengths `{3, 2}`, then the
two word RAM programs of `Sanity`. Every instance the explicit maps produce has release times
and deadlines at most `27` times the number of its jobs (`SatConstruction.times_le`,
`StackedConstruction.times_le`), so the emitted word has every number linear in its length.

The injectivity of the encodings (`Inj`) is taken from the proof package of lax-391470
(`Lax391470Proofs.Encoding`), which is not a dependency of this package; only the namespace
is changed.
-/

namespace Lax434175Proofs.SanityStrong.Inj

open Lax391470 Lax391470.BinaryEncoding Lax434930.PolynomialTime

/-- A code is *prefix-free*: a code word followed by anything determines both. -/
def PrefixFree {α : Type} (e : α → Word) : Prop :=
  ∀ a b x y, e a ++ x = e b ++ y → a = b ∧ x = y

def ofBits : List Bool → ℕ := List.foldr (fun b n => Nat.bit b n) 0

lemma ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ofBits]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [ofBits, List.foldr_cons] at ih ⊢
    rw [ih]

lemma bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← ofBits_bits a, ← ofBits_bits b, h]

lemma replicate_true_inj (a b : ℕ) (u v : Word)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using h
    | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ] at h
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih b h
      exact ⟨by omega, h2⟩

lemma encodeNat_prefixFree : PrefixFree encodeNat := by
  intro a b x y h
  simp only [encodeNat, List.append_assoc, List.singleton_append] at h
  obtain ⟨hl, hr⟩ := replicate_true_inj _ _ _ _ h
  obtain ⟨hb, hxy⟩ := List.append_inj hr hl
  exact ⟨bits_injective hb, hxy⟩

/-- Two prefix-free codes in sequence are prefix-free. -/
lemma PrefixFree.pair {α β : Type} {e : α → Word} {f : β → Word} (he : PrefixFree e)
    (hf : PrefixFree f) : PrefixFree fun ab : α × β => e ab.1 ++ f ab.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ x y h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h2⟩ := he _ _ _ _ h
  obtain ⟨h3, h4⟩ := hf _ _ _ _ h2
  exact ⟨by rw [h1, h3], h4⟩

lemma bool_prefixFree : PrefixFree fun b : Bool => [b] := by
  intro a b x y h
  simpa using h

/-- A sequence of `n` code words of a prefix-free code determines its entries. -/
lemma flatMap_inj {α : Type} {e : α → Word} (he : PrefixFree e) :
    ∀ (n : ℕ) (f g : Fin n → α) (x y : Word),
      (List.finRange n).flatMap (fun i => e (f i)) ++ x =
        (List.finRange n).flatMap (fun i => e (g i)) ++ y → f = g ∧ x = y := by
  intro n
  induction n with
  | zero => intro f g x y h; exact ⟨funext fun i => i.elim0, by simpa using h⟩
  | succ n ih =>
    intro f g x y h
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.append_assoc] at h
    obtain ⟨h0, hrest⟩ := he _ _ _ _ h
    obtain ⟨hfg, hxy⟩ := ih (fun i => f i.succ) (fun i => g i.succ) x y hrest
    refine ⟨funext fun i => ?_, hxy⟩
    refine Fin.cases h0 (fun j => ?_) i
    exact congrFun hfg j

theorem encodeAux_injective : Function.Injective encodeAux := by
  rintro ⟨n, r, d, l, N, a, b, c, e⟩ ⟨n', r', d', l', N', a', b', c', e'⟩ h
  simp only [encodeAux, List.append_assoc] at h
  obtain ⟨hn, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨hN, h⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hn; subst hN
  have hc1 := (encodeNat_prefixFree.pair encodeNat_prefixFree).pair bool_prefixFree
  obtain ⟨hf, h⟩ := flatMap_inj hc1 n (fun o => ((r o, d o), l o))
    (fun o => ((r' o, d' o), l' o)) _ _ (by simpa using h)
  have hc2 := ((encodeNat_prefixFree.pair encodeNat_prefixFree).pair encodeNat_prefixFree).pair
    encodeNat_prefixFree
  obtain ⟨hg, -⟩ := flatMap_inj hc2 N (fun i => (((a i, b i), c i), e i))
    (fun i => (((a' i, b' i), c' i), e' i)) [] [] (by simpa using h)
  have hr : r = r' := funext fun j => by have := congrFun hf j; simp_all
  have hd : d = d' := funext fun j => by have := congrFun hf j; simp_all
  have hl : l = l' := funext fun j => by have := congrFun hf j; simp_all
  have ha : a = a' := funext fun j => by have := congrFun hg j; simp_all
  have hb : b = b' := funext fun j => by have := congrFun hg j; simp_all
  have hcc : c = c' := funext fun j => by have := congrFun hg j; simp_all
  have he : e = e' := funext fun j => by have := congrFun hg j; simp_all
  rw [hr, hd, hl, ha, hb, hcc, he]

end Lax434175Proofs.SanityStrong.Inj

namespace Lax434175Proofs.SanityStrong

open Lax391470 Lax391470.BinaryEncoding
open Lax434175 Lax434175.Results
open Lax434175Proofs.Sanity Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan
open Lax434175Proofs.Sanity.InstFormat Lax434175Proofs.Sanity.Parse Lax434175Proofs.Sanity.TokProg
open Lax434175Proofs.Sanity.Emit Lax434175Proofs.Sanity.Correct
open Lax888481Proofs.Theorem2Assembly (natBits bitsOf bitsOf_natBits)

/-! ### Words of instances with small numbers -/

/-- Every time and processing time of `I` is at most `K` times one more than its number of
jobs. -/
def Bnd (K : ℕ) (I : Scheduling.Instance) : Prop :=
  ∀ j, (I.r j).natAbs ≤ K * (I.jobs + 1) ∧ (I.d j).natAbs ≤ K * (I.jobs + 1) ∧
    I.p j ≤ K * (I.jobs + 1)

/-- Reading the tokens of the code of an instance gives the values of its tokens. -/
theorem parse_encode (I : Scheduling.Instance) :
    parseF (natBits (encodeInstance I)) = vals (toksOf I) := by
  unfold parseF
  rw [bitsOf_natBits]
  obtain ⟨hacc, htoks⟩ := accept_complete EI (toksOf I) (conforms_toksOf I)
  rw [← encodeInstance_eq] at hacc htoks
  rw [if_pos ((acc_iff _).mpr hacc), htoks]

theorem vals_le (I : Scheduling.Instance) (B : ℕ) (h1 : 1 ≤ B) (hn : I.jobs ≤ B)
    (hb : ∀ j, (I.r j).natAbs ≤ B ∧ (I.d j).natAbs ≤ B ∧ I.p j ≤ B) :
    ∀ v ∈ vals (toksOf I), v ≤ B := by
  intro v hv
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hn
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp ht
  unfold jobRec at hj
  split_ifs at hj with hjn
  · obtain ⟨h1', h2', h3'⟩ := hb ⟨j, hjn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [Tok.val] <;>
      first | omega | (split_ifs <;> omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [Tok.val]

theorem stdWord_length (R : Raw) : R.jobs ≤ (stdWord R).length := by
  unfold stdWord stdInst
  simp only [List.length_append]
  rw [RecList.length_flatMap_const (fun j => [R.r j, 1, R.d j]) 3 (fun _ => rfl)]
  omega

/-- **The emitted word of an instance with small numbers is small.** -/
theorem emit_small (I : Scheduling.Instance) (K : ℕ) (hK : 1 ≤ K) (hb : Bnd K I) :
    emitF (vals (toksOf I)) ∈ Small (2 * K + 16) 1 := by
  set z := vals (toksOf I)
  have hz : ∀ v ∈ z, v ≤ K * (I.jobs + 1) :=
    vals_le I _ (by nlinarith) (by nlinarith) hb
  have hM : maxEntry z ≤ K * (I.jobs + 1) := Lax434175Proofs.ThresholdWords.maxEntry_le hz
  intro v hv
  have hv' := emitF_le z v hv
  rw [pow_one]
  by_cases hok : okW z
  · have hL : I.jobs ≤ (emitF z).length := by
      unfold emitF; rw [if_pos hok]
      have := stdWord_length (rawW z)
      have h0 : (rawW z).jobs = I.jobs := g_zero I
      omega
    nlinarith
  · unfold emitF at hv; rw [if_neg hok] at hv
    simp only [noWord, List.mem_cons, List.not_mem_nil, or_false] at hv
    have : 1 ≤ (2 * K + 16) * ((emitF z).length + 1) := by nlinarith
    omega

/-! ### The numbers of the explicit reductions of lax-391470 -/

/-- The stacked instance of an ordered instance whose times are at most `T`. -/
theorem stacked_bnd (A : AuxiliaryProblem.Instance) (hA : A.Ordered) (T K : ℕ)
    (hT : (∀ o, A.r o ≤ T ∧ A.d o ≤ T) ∧ (∀ i, A.longDue i ≤ T ∧ A.shortDue i ≤ T))
    (hK : 3 ≤ K) (hTK : T + 7 * A.pairs ≤ K * (StackedConstruction.numJobs A + 1)) :
    Bnd K (StackedConstruction.inst 3 2 A) := by
  intro j
  obtain ⟨hr, hd⟩ := StackedConstruction.times_le 3 2 A hA T hT j
  rw [Int.abs_eq_natAbs] at hr hd
  have hr' : ((StackedConstruction.inst 3 2 A).r j).natAbs ≤ T + 7 * A.pairs := by
    exact_mod_cast hr
  have hd' : ((StackedConstruction.inst 3 2 A).d j).natAbs ≤ T + 7 * A.pairs := by
    exact_mod_cast hd
  have hp := StackedConstruction.lengthsIn 3 2 A j
  have hJ : (StackedConstruction.inst 3 2 A).jobs = StackedConstruction.numJobs A := rfl
  rw [hJ]
  refine ⟨hr'.trans hTK, hd'.trans hTK, ?_⟩
  have : 3 ≤ K * (StackedConstruction.numJobs A + 1) := by nlinarith
  omega

theorem one_le_numVars (F : Lax429075.CNF.Formula) : 1 ≤ SatConstruction.numVars F := by
  unfold SatConstruction.numVars
  induction F.flatMap id with
  | nil => exact le_refl _
  | cons a l ih => exact le_max_of_le_right ih

/-- The time line of the formula instance is linear in its number of pairs. -/
theorem sat_le (F : Lax429075.CNF.Formula) :
    2 * SatConstruction.numVars F * SatConstruction.sectionLength 3 2 F +
        7 * SatConstruction.numPairs F ≤
      27 * (SatConstruction.numOrdinary F + 5 * SatConstruction.numPairs F + 1) := by
  unfold SatConstruction.sectionLength SatConstruction.numPairs SatConstruction.numOrdinary
  obtain ⟨k, hk⟩ : ∃ k, SatConstruction.numVars F = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (one_le_numVars F)).symm⟩
  rw [hk, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  set m := SatConstruction.numClauses F
  nlinarith [Nat.zero_le (k * m)]

/-- **Every instance the explicit reductions produce has small numbers.** -/
theorem reduce_bnd (y : Lax434930.PolynomialTime.Word) :
    ∃ I, Lemma1.reduce 3 2 (Lemma2.reduce 3 2 y) = encodeInstance I ∧ Bnd 27 I := by
  unfold Lemma1.reduce
  split_ifs with h
  · obtain ⟨he, ho⟩ := h.choose_spec
    refine ⟨_, rfl, ?_⟩
    generalize h.choose = A at he ho ⊢
    cases hd : Lax429075.Encoding.decodeCNF y with
    | none =>
      simp only [Lemma2.reduce, hd] at he
      obtain rfl := Inj.encodeAux_injective he
      refine stacked_bnd _ ho 0 27 ⟨fun o => ⟨le_refl _, le_refl _⟩, fun i => i.elim0⟩
        (by norm_num) (by simp [Lemma2.blocked, StackedConstruction.numJobs])
    | some F =>
      simp only [Lemma2.reduce, hd] at he
      obtain rfl := Inj.encodeAux_injective he
      exact stacked_bnd _ ho _ 27 (SatConstruction.times_le 3 2 F) (by norm_num) (sat_le F)
  · refine ⟨Lemma1.blocked 3, rfl, fun j => ?_⟩
    simp [Lemma1.blocked]

/-- `1|r_j|L_max` on the standard reading. -/
theorem key_strong (y : Lax434930.PolynomialTime.Word) :
    emitF (parseF (natBits (Lemma1.reduce 3 2 (Lemma2.reduce 3 2 y)))) ∈ Small (2 * 27 + 16) 1 := by
  obtain ⟨I, hI, hb⟩ := reduce_bnd y
  rw [hI, parse_encode]
  exact emit_small I 27 (by norm_num) hb

/--
---
conclusion: Lax434175.SanityParams.p158_r0_holds
---
The reduction of `Sanity.npHard_rjLmax` through the explicit maps of lax-391470, whose
instances have every time at most `27` times the number of jobs.
-/
theorem p158_r0_holds : Lax434175.ZooParallelResults.p158_r0 Lax434175.StandardReading.ops := by
  show Lax434175.Results.StronglyNPHard _
  refine ⟨2 * 27 + 16, 1, fun A hA => ?_⟩
  obtain ⟨fS, ⟨tS⟩, hS⟩ := Lax429075.SATHard.hardness A hA
  obtain ⟨t2⟩ := Lemma2.reduce_polyTime 3 2
  obtain ⟨t1⟩ := Lemma1.reduce_polyTime 3 2
  obtain ⟨tN⟩ := Lax888481Proofs.TMToNats.toNats
  obtain ⟨tP⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Parse.parseF_polytime
  obtain ⟨tE⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Emit.emitF_polytime
  obtain ⟨c1⟩ := Lax888481Proofs.TMCompose.comp tS t2
  obtain ⟨c2⟩ := Lax888481Proofs.TMCompose.comp c1 t1
  obtain ⟨c3⟩ := Lax888481Proofs.TMCompose.comp c2 tN
  obtain ⟨c4⟩ := Lax888481Proofs.TMCompose.comp c3 tP
  obtain ⟨c5⟩ := Lax888481Proofs.TMCompose.comp c4 tE
  refine ⟨_, ⟨c5⟩, fun x => ⟨⟨emitF_domain _, key_strong (fS x)⟩, ?_⟩⟩
  exact (hS x).trans ((Lemma2.reduce_correct 3 2 (by norm_num) (by norm_num) _).trans
    ((Lemma1.reduce_correct 3 2 (by norm_num) (by norm_num) _).trans (Correct.key _)))

end Lax434175Proofs.SanityStrong
