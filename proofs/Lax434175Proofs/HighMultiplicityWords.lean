import Mathlib.Tactic
import Lax434175Proofs.HighMultiplicityMap
import Lax434175Proofs.PropagationStandard
import Lax434175Proofs.P200Words
import Lax434175Proofs.IsemStandard
import Lax434175Proofs.Determined
import Lax434175Proofs.IsemPrograms

/-!
The word map `hmWord` on the words of instances.

**Sorting by ranks.** Let `F` be a list-valued function on the indices below `n`, call an index
*first* if no smaller index has the same value, and let the rank of an index be the number of
first indices with a smaller value. Listing, for `r = 0, 1, …`, the values of the first
indices of rank `r` lists every value once, in increasing order, and lists as many values as
there are first indices (`sortS_lists`, `sortS_length`). For `hmWord` the value of job `j` is
its tuple with the number of jobs that have it in front, so `hmWord` writes `[1, n, m]`, the
canonical block of these values, the two blocks it copies and the threshold
(`hmWord_eq`).

**Standard words.** On the standard word of an instance (`hsrc`: the records, the two blocks,
the release dates, weights and due dates, the threshold), the tuple of job `j` is its record
followed by its three numbers, so the values are the type tuples of the instance. If the
instance has no facts on pairs of jobs, the image is the high-multiplicity word of the
instance, read with the more general values of a specification with high multiplicity
(`hmWord_encodes`).

**Parameters.** Two instances written by one high-multiplicity word have the same number of
machines and the same type tuples; every job has a record, so the processing times of the
operations of one are those of the other (`numP_le`).
-/

namespace Lax434175Proofs.HighMultiplicityWords
open Lax434175Proofs.P200Programs (nA posA psum psum_succ psum_mono psum_congr psum_const
  length_flatMap_range getD_flatMap_range gA getD_app eq_of_getD)
open Lax434175Proofs.IsemPrograms (filter_range_succ flatMap_filter_eq)
open Lax434175Proofs.HighMultiplicityMap
open Lax434175.StandardReading

/-! ### Sorting by ranks -/

theorem filter_length_le {p q : ℕ → Bool} : ∀ (n : ℕ), (∀ i < n, p i = true → q i = true) →
    ((List.range n).filter p).length ≤ ((List.range n).filter q).length
  | 0, _ => by simp
  | n + 1, h => by
    rw [filter_range_succ, filter_range_succ]
    have := filter_length_le n fun i hi => h i (by omega)
    by_cases hp : p n = true
    · simp [hp, h n (by omega) hp]; omega
    · simp only [hp, Bool.false_eq_true, if_false]; split_ifs <;> omega

theorem filter_length_lt {p q : ℕ → Bool} : ∀ (n : ℕ), (∀ i < n, p i = true → q i = true) →
    ∀ i₀ < n, q i₀ = true → p i₀ = false →
      ((List.range n).filter p).length < ((List.range n).filter q).length
  | 0, _, _, h, _, _ => by omega
  | n + 1, h, i₀, hi, hq, hp => by
    rw [filter_range_succ, filter_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have := filter_length_lt n (fun i hi => h i (by omega)) i₀ hi hq hp
      by_cases hp' : p n = true
      · simp [hp', h n (by omega) hp']; omega
      · simp only [hp', Bool.false_eq_true, if_false]; split_ifs <;> omega
    · have := filter_length_le i₀ fun i hi => h i (by omega)
      simp [hq, hp]; omega

section Ranks
variable (n : ℕ) (F : ℕ → List ℕ) (fst : ℕ → Bool) (less : ℕ → ℕ → Bool)

/-- The rank of `j`: the first indices with a smaller value. -/
def rkS (j : ℕ) : ℕ := ((List.range n).filter fun i => fst i && less i j).length

/-- The first indices of rank `r`. -/
def atRank (r : ℕ) : List ℕ := (List.range n).filter fun j => fst j && rkS n fst less j == r

/-- The values of the first indices, by rank. -/
def sortS : List (List ℕ) := (List.range n).flatMap fun r => (atRank n fst less r).map F

variable {n F fst less}
variable (hfst : ∀ j < n, fst j = true ↔ ∀ i < j, F i ≠ F j)
  (hless : ∀ i < n, ∀ j < n, less i j = true ↔ F i < F j)
include hfst

theorem first_exists : ∀ j < n, ∃ i ≤ j, fst i = true ∧ F i = F j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h : fst j = true
    · exact ⟨j, le_rfl, h, rfl⟩
    · obtain ⟨i, hi, he⟩ : ∃ i < j, F i = F j := by
        by_contra hc
        push Not at hc
        exact h ((hfst j hj).mpr hc)
      obtain ⟨i', hi', hf, he'⟩ := ih i hi (by omega)
      exact ⟨i', by omega, hf, he'.trans he⟩

theorem first_unique {i j : ℕ} (hi : i < n) (hj : j < n) (fi : fst i = true) (fj : fst j = true)
    (h : F i = F j) : i = j := by
  rcases lt_trichotomy i j with hl | rfl | hl
  · exact absurd h ((hfst j hj).mp fj i hl)
  · rfl
  · exact absurd h.symm ((hfst i hi).mp fi j hl)

omit hfst in
include hless in
theorem rkS_lt_of_lt {i j : ℕ} (hi : i < n) (hj : j < n) (fi : fst i = true) (h : F i < F j) :
    rkS n fst less i < rkS n fst less j :=
  filter_length_lt n (fun k hk hp => by
    simp only [Bool.and_eq_true] at hp ⊢
    exact ⟨hp.1, (hless k hk j hj).mpr (((hless k hk i hi).mp hp.2).trans h)⟩) i hi
    (by simp [fi, (hless i hi j hj).mpr h]) (by simp [(hless i hi i hi).not.mpr (lt_irrefl _)])

omit hfst in
include hless in
theorem rkS_lt (j : ℕ) (hj : j < n) : rkS n fst less j < n := by
  have := filter_length_lt (p := fun i => fst i && less i j) (q := fun _ => true) n
    (fun _ _ _ => rfl) j hj rfl (by simp [(hless j hj j hj).not.mpr (lt_irrefl _)])
  simpa [rkS] using this

include hless in
theorem rank_inj {i j : ℕ} (hi : i < n) (hj : j < n) (fi : fst i = true) (fj : fst j = true)
    (h : rkS n fst less i = rkS n fst less j) : i = j := by
  rcases lt_trichotomy (F i) (F j) with hl | he | hl
  · exact absurd h (rkS_lt_of_lt hless hi hj fi hl).ne
  · exact first_unique hfst hi hj fi fj he
  · exact absurd h (rkS_lt_of_lt hless hj hi fj hl).ne'

omit hfst in
theorem mem_atRank {r j : ℕ} : j ∈ atRank n fst less r ↔ j < n ∧ fst j = true ∧ rkS n fst less j = r := by
  simp [atRank]

include hless in
theorem mem_sortS (t : List ℕ) : t ∈ sortS n F fst less ↔ ∃ j < n, F j = t := by
  simp only [sortS, List.mem_flatMap, List.mem_map, List.mem_range, mem_atRank]
  constructor
  · rintro ⟨r, -, j, ⟨hj, -, -⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨i, hi, hf, he⟩ := first_exists hfst j hj
    exact ⟨rkS n fst less i, rkS_lt hless i (by omega), i, ⟨by omega, hf, rfl⟩, he⟩

include hless in
theorem sortS_pairwise : (sortS n F fst less).Pairwise (· < ·) := by
  rw [sortS, List.pairwise_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine ((List.pairwise_lt_range (n := n)).filter _).imp_of_mem fun {a b} ha hb hab => ?_
    obtain ⟨ha, fa, ra⟩ := (mem_atRank).mp ha
    obtain ⟨hb, fb, rb⟩ := (mem_atRank).mp hb
    exact absurd (rank_inj hfst hless ha hb fa fb (ra.trans rb.symm)) hab.ne
  · refine (List.pairwise_lt_range (n := n)).imp_of_mem fun {r₁ r₂} _ _ hr => ?_
    simp only [List.mem_map, mem_atRank]
    rintro _ ⟨j₁, ⟨h₁, f₁, rfl⟩, rfl⟩ _ ⟨j₂, ⟨h₂, f₂, rfl⟩, rfl⟩
    rcases lt_trichotomy (F j₁) (F j₂) with hl | he | hl
    · exact hl
    · exact absurd (first_unique hfst h₁ h₂ f₁ f₂ he ▸ hr) (lt_irrefl _)
    · exact absurd (rkS_lt_of_lt hless h₂ h₁ f₂ hl) (by omega)

include hless in
/-- **The values by rank write the set of values.** -/
theorem sortS_lists : Lists {t | ∃ j < n, F j = t} (sortS n F fst less) :=
  ⟨sortS_pairwise hfst hless, fun t => mem_sortS hfst hless t⟩

omit hfst in
include hless in
/-- **As many values as first indices.** -/
theorem sortS_length : (sortS n F fst less).length = ((List.range n).filter fst).length := by
  have hperm : ((List.range n).flatMap (atRank n fst less)).Perm ((List.range n).filter fst) := by
    refine (List.perm_ext_iff_of_nodup ?_ ((List.nodup_range).filter _)).mpr fun j => ?_
    · refine List.nodup_flatMap.mpr ⟨fun r _ => (List.nodup_range).filter _, ?_⟩
      refine (List.nodup_range (n := n)).imp_of_mem fun {r₁ r₂} _ _ hr => ?_
      intro j h₁ h₂
      exact hr (((mem_atRank).mp h₁).2.2.symm.trans ((mem_atRank).mp h₂).2.2)
    · simp only [List.mem_flatMap, List.mem_range, mem_atRank, List.mem_filter]
      constructor
      · rintro ⟨r, -, hj, hf, -⟩; exact ⟨hj, hf⟩
      · rintro ⟨hj, hf⟩; exact ⟨_, rkS_lt hless j hj, hj, hf, rfl⟩
  rw [sortS, ← List.map_flatMap, List.length_map, hperm.length_eq]

end Ranks

/-! ### The shape of the image -/

section Shape
variable (u : List ℕ)

/-- The tuple of job `j` with the number of jobs that have it in front. -/
def fullH (j : ℕ) : List ℕ := cntH u j :: tupH u j

/-- The distinct extended tuples, by rank. -/
def typesH : List (List ℕ) := sortS (nA u) (fullH u) (fstH u) (lessH u)

theorem cntH_congr {i j : ℕ} (h : tupH u i = tupH u j) : cntH u i = cntH u j := by
  unfold cntH; rw [h]

theorem fullH_ne_iff (i j : ℕ) : fullH u i ≠ fullH u j ↔ tupH u i ≠ tupH u j := by
  unfold fullH
  constructor
  · intro h he; exact h (by rw [cntH_congr u he, he])
  · intro h he; exact h (List.cons.inj he).2

theorem fstH_iff {j : ℕ} (hj : j < nA u) : fstH u j = true ↔ ∀ i < j, fullH u i ≠ fullH u j := by
  simp only [fstH, Bool.not_eq_true', List.any_eq_false, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, not_and, cmpL_eq_zero, fullH_ne_iff]
  constructor
  · intro h i hi; exact h i (by omega) hi
  · intro h i _ hi; exact h i hi

theorem lessH_iff (i j : ℕ) : lessH u i j = true ↔ fullH u i < fullH u j := by
  simp only [lessH, fullH, List.cons_lt_cons_iff, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, beq_iff_eq, cmpL_eq_one]

/-- **The image lists the distinct extended tuples.** -/
theorem typesH_lists : Lists {t | ∃ j < nA u, fullH u j = t} (typesH u) :=
  sortS_lists (fun _ hj => fstH_iff u hj) (fun i _ j _ => lessH_iff u i j)

theorem typesH_length : (typesH u).length = ddH u :=
  sortS_length (fun i _ j _ => lessH_iff u i j)

/-- **The shape of the image**: the header, the canonical block of the extended tuples, the
two blocks and the threshold. -/
theorem hmWord_eq : hmWord u = [1, u.getD 1 0, u.getD 2 0] ++ flat (typesH u) ++ midH u ++
    [u.getD (u.length - 2) 0, u.getD (u.length - 1) 0] := by
  have hf : (typesH u).flatMap (fun t => t.length :: t) =
      (List.range (nA u)).flatMap (fun r => (List.range (nA u)).flatMap (outH u r)) := by
    rw [typesH, sortS, List.flatMap_assoc]
    refine List.flatMap_congr fun r _ => ?_
    rw [atRank, List.flatMap_map, flatMap_filter_eq]
    refine List.flatMap_congr fun j _ => ?_
    simp only [outH, fullH, List.length_cons, tupH_length]
    rfl
  rw [hmWord, flat, typesH_length, hf]
  simp

end Shape

/-! ### Standard words -/

/-- A standard word: `n` records, each preceded by its length, then `Z` (the two blocks), the
triples `O` of the jobs, and the threshold. -/
def hsrc (n m : ℕ) (R O : ℕ → List ℕ) (Z : List ℕ) (sg ab : ℕ) : List ℕ :=
  [0, n, m] ++ ((List.range n).flatMap (fun j => (R j).length :: R j) ++
    (Z ++ ((List.range n).flatMap O ++ [sg, ab])))

section Src
variable (n m : ℕ) (R O : ℕ → List ℕ) (Z : List ℕ) (sg ab : ℕ)

/-- The length of the records of the first `j` jobs. -/
abbrev rp (j : ℕ) : ℕ := psum (fun k => (R k).length + 1) j

theorem length_recs : ((List.range n).flatMap (fun j => (R j).length :: R j)).length = rp R n :=
  length_flatMap_range _ n

theorem getD_recs {j t : ℕ} (hj : j < n) (ht : t < (R j).length + 1) :
    ((List.range n).flatMap (fun j => (R j).length :: R j)).getD (rp R j + t) 0 =
      ((R j).length :: R j).getD t 0 :=
  getD_flatMap_range (fun j => (R j).length :: R j) hj ht

theorem rp_le {j : ℕ} (hj : j < n) : rp R j + (R j).length + 1 ≤ rp R n := by
  have := psum_mono (fun k => (R k).length + 1) (show j + 1 ≤ n by omega)
  rw [psum_succ] at this
  simp only [rp]; omega

variable {n O} (hO : ∀ j < n, (O j).length = 3)
include hO

theorem length_objs : ((List.range n).flatMap O).length = 3 * n := by
  rw [length_flatMap_range, psum_congr (g := fun _ => 3) (fun k hk => hO k hk), psum_const]

theorem getD_objs {j t : ℕ} (hj : j < n) (ht : t < 3) :
    ((List.range n).flatMap O).getD (3 * j + t) 0 = (O j).getD t 0 := by
  have e : 3 * j = psum (fun k => (O k).length) j := by
    rw [psum_congr (g := fun _ => 3) (fun k hk => hO k (by omega)), psum_const, mul_comm]
  rw [e]
  exact getD_flatMap_range O hj (by rw [hO j hj]; exact ht)

theorem length_hsrc : (hsrc n m R O Z sg ab).length = 3 + rp R n + Z.length + 3 * n + 2 := by
  simp only [hsrc, List.length_append, length_recs, length_objs hO, List.length_cons, List.length_nil]
  omega

omit hO in
theorem getD_hsrc_rec {j k : ℕ} (hj : j < n) (hk : k < (R j).length + 1) :
    (hsrc n m R O Z sg ab).getD (3 + rp R j + k) 0 = ((R j).length :: R j).getD k 0 := by
  have h1 := rp_le n R hj
  rw [hsrc, show 3 + rp R j + k = [0, n, m].length + (rp R j + k) by simp; omega, getD_app,
    List.getD_append _ _ _ _ (by rw [length_recs]; omega), getD_recs n R hj hk]

omit hO in
theorem getD_hsrc_Z {k : ℕ} (hk : k < Z.length) :
    (hsrc n m R O Z sg ab).getD (3 + rp R n + k) 0 = Z.getD k 0 := by
  rw [hsrc, show 3 + rp R n + k = [0, n, m].length + (rp R n + k) by simp; omega, getD_app,
    ← length_recs n R, getD_app, List.getD_append _ _ _ _ hk]

theorem getD_hsrc_obj {j k : ℕ} (hj : j < n) (hk : k < 3) :
    (hsrc n m R O Z sg ab).getD (3 + rp R n + Z.length + (3 * j + k)) 0 = (O j).getD k 0 := by
  rw [hsrc, show 3 + rp R n + Z.length + (3 * j + k) = [0, n, m].length + (rp R n + (Z.length +
    (3 * j + k))) by simp; omega, getD_app, ← length_recs n R, getD_app, getD_app,
    List.getD_append _ _ _ _ (by rw [length_objs hO]; omega), getD_objs hO hj hk]

theorem getD_hsrc_sg : (hsrc n m R O Z sg ab).getD ((hsrc n m R O Z sg ab).length - 2) 0 = sg := by
  rw [length_hsrc m R Z sg ab hO, hsrc, show 3 + rp R n + Z.length + 3 * n + 2 - 2 = [0, n, m].length +
    (rp R n + (Z.length + (3 * n + 0))) by simp; omega, getD_app, ← length_recs n R, getD_app, getD_app,
    ← length_objs hO, getD_app]
  rfl

theorem getD_hsrc_ab : (hsrc n m R O Z sg ab).getD ((hsrc n m R O Z sg ab).length - 1) 0 = ab := by
  rw [length_hsrc m R Z sg ab hO, hsrc, show 3 + rp R n + Z.length + 3 * n + 2 - 1 = [0, n, m].length +
    (rp R n + (Z.length + (3 * n + 1))) by simp; omega, getD_app, ← length_recs n R, getD_app, getD_app,
    ← length_objs hO, getD_app]
  rfl

theorem nA_hsrc : nA (hsrc n m R O Z sg ab) = n := by
  unfold nA
  rw [length_hsrc m R Z sg ab hO]
  simp only [hsrc, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
  omega

omit hO in
theorem getD_hsrc_one : (hsrc n m R O Z sg ab).getD 1 0 = n := rfl

omit hO in
theorem getD_hsrc_two : (hsrc n m R O Z sg ab).getD 2 0 = m := rfl

omit hO in
theorem posA_hsrc : ∀ j ≤ n, posA (hsrc n m R O Z sg ab) j = 3 + rp R j
  | 0, _ => rfl
  | j + 1, hj => by
    show posA (hsrc n m R O Z sg ab) j + 1 + (hsrc n m R O Z sg ab).getD
      (posA (hsrc n m R O Z sg ab) j) 0 = _
    rw [posA_hsrc j (by omega), show 3 + rp R j = 3 + rp R j + 0 from rfl,
      getD_hsrc_rec m R Z sg ab (by omega) (by omega)]
    simp only [List.getD_cons_zero, rp, psum_succ]
    omega

theorem lnH_hsrc {j : ℕ} (hj : j < n) : lnH (hsrc n m R O Z sg ab) j = (R j).length := by
  unfold lnH
  rw [posA_hsrc m R Z sg ab j hj.le, show 3 + rp R j = 3 + rp R j + 0 from rfl,
    getD_hsrc_rec m R Z sg ab hj (by omega), length_hsrc m R Z sg ab hO]
  have := rp_le n R hj
  simp only [List.getD_cons_zero]
  omega

theorem obH_hsrc : obH (hsrc n m R O Z sg ab) = 3 + rp R n + Z.length := by
  unfold obH
  rw [nA_hsrc m R Z sg ab hO, length_hsrc m R Z sg ab hO]
  omega

theorem tupH_hsrc {j : ℕ} (hj : j < n) : tupH (hsrc n m R O Z sg ab) j = R j ++ O j := by
  refine eq_of_getD (by rw [tupH_length, lnH_hsrc m R Z sg ab hO hj, List.length_append, hO j hj])
    fun k hk => ?_
  rw [tupH_getD _ _ hk]
  rw [tupH_length, lnH_hsrc m R Z sg ab hO hj] at hk
  unfold idxH
  rw [lnH_hsrc m R Z sg ab hO hj]
  split_ifs with h
  · rw [posA_hsrc m R Z sg ab j hj.le, show 3 + rp R j + 1 + k = 3 + rp R j + (k + 1) by omega,
      getD_hsrc_rec m R Z sg ab hj (by omega), List.getD_append _ _ _ _ h]
    rfl
  · rw [obH_hsrc m R Z sg ab hO, show 3 + rp R n + Z.length + 3 * j + (k - (R j).length) =
      3 + rp R n + Z.length + (3 * j + (k - (R j).length)) by omega,
      getD_hsrc_obj m R Z sg ab hO hj (by omega), List.getD_append_right _ _ _ _ (by omega)]

theorem midH_hsrc : midH (hsrc n m R O Z sg ab) = Z := by
  unfold midH
  rw [obH_hsrc m R Z sg ab hO, nA_hsrc m R Z sg ab hO, posA_hsrc m R Z sg ab n le_rfl,
    show 3 + rp R n + Z.length - (3 + rp R n) = Z.length by omega]
  conv_rhs => rw [← Lax434175Proofs.P200Programs.map_range_getD Z]
  exact List.map_congr_left fun k hk => getD_hsrc_Z m R Z sg ab (List.mem_range.mp hk)

/-- **The image of a standard word.** -/
theorem hmWord_hsrc : hmWord (hsrc n m R O Z sg ab) =
    [1, n, m] ++ flat (typesH (hsrc n m R O Z sg ab)) ++ Z ++ [sg, ab] := by
  rw [hmWord_eq, midH_hsrc m R Z sg ab hO, getD_hsrc_sg m R Z sg ab hO, getD_hsrc_ab m R Z sg ab hO]
  rfl

theorem cntH_hsrc {j : ℕ} (hj : j < n) : cntH (hsrc n m R O Z sg ab) j =
    ((List.range n).filter fun i => decide (R i ++ O i = R j ++ O j)).length := by
  unfold cntH
  rw [nA_hsrc m R Z sg ab hO]
  congr 1
  refine List.filter_congr fun i hi => ?_
  rw [tupH_hsrc m R Z sg ab hO (List.mem_range.mp hi), tupH_hsrc m R Z sg ab hO hj, Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact cmpL_eq_zero _ _

end Src

/-! ### The words of instances -/

section Inst
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results

/-- The number of indices with a property, as the length of a filter. -/
theorem natCard_eq_filter {n : ℕ} (P : Fin n → Prop) (q : ℕ → Bool)
    (hq : ∀ i (h : i < n), q i = true ↔ P ⟨i, h⟩) :
    Nat.card {j // P j} = ((List.range n).filter q).length := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e : (Finset.univ.filter P).map Fin.valEmbedding = ((List.range n).filter q).toFinset := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j.isLt, (hq j j.isLt).mpr hj⟩
    · rintro ⟨hi, hqi⟩; exact ⟨⟨i, hi⟩, (hq i hi).mp hqi, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e,
    List.toFinset_card_of_nodup ((List.nodup_range).filter _)]

variable {s : Spec OperationsFamily.family} (x : Inst OperationsFamily.family s)

/-- The records of the jobs, on the naturals. -/
def recN (R : Fin x.base.jobs → List ℕ) (j : ℕ) : List ℕ :=
  if h : j < x.base.jobs then R ⟨j, h⟩ else []

/-- The release date, weight and due date of job `j`, on the naturals. -/
def objN (j : ℕ) : List ℕ := if h : j < x.base.jobs then objOf x ⟨j, h⟩ else []

theorem objN_length {j : ℕ} (hj : j < x.base.jobs) : (objN x j).length = 3 := by
  simp [objN, hj, objOf]

/-- **The standard word of an instance.** -/
theorem word_std (hs : s.module .encoding = .standard) {u : List ℕ} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at s) u x D) :
    ∃ R b₂ b₃, (∀ j, Record x j (R j)) ∧ Block (pairTuples x) b₂ ∧ Block (globalTuples x) b₃ ∧
      u = hsrc x.base.jobs x.base.machines (recN x R) (objN x) (b₂ ++ b₃)
        (if D < 0 then 1 else 0) D.natAbs := by
  obtain ⟨w, rfl, b₂, b₃, hb₂, hb₃, hcase⟩ := hx
  rcases hcase with ⟨-, b₁, ⟨R, hR, rfl⟩, rfl⟩ | ⟨hhm, -⟩
  · refine ⟨R, b₂, b₃, hR, hb₂, hb₃, ?_⟩
    have e1 : (List.ofFn fun j => (R j).length :: R j).flatten =
        (List.range x.base.jobs).flatMap fun j => (recN x R j).length :: recN x R j := by
      rw [Lax434175Proofs.IsemWords.ofFn_eq_range]
      exact List.flatMap_congr fun j hj => by simp [recN, List.mem_range.mp hj]
    have e2 : objWord x = (List.range x.base.jobs).flatMap (objN x) :=
      Lax434175Proofs.IsemWords.ofFn_eq_range _
    rw [e1, e2]
    simp only [hsrc, List.append_assoc]
  · exact ForbiddenTimes.Encoding.noConfusion (hs.symm.trans hhm)

variable {x} {R : Fin x.base.jobs → List ℕ}

theorem record_iff (hR : ∀ j, Record x j (R j)) (j : Fin x.base.jobs) (b : List ℕ) :
    Record x j b ↔ b = R j :=
  ⟨fun h => Lax434175Proofs.P200Words.record_unique x j h (hR j), fun h => h ▸ hR j⟩

/-- **The extended tuples of the standard word are the type tuples of the instance.** -/
theorem typeTuples_hsrc (hR : ∀ j, Record x j (R j)) (Z : List ℕ) (sg ab : ℕ) :
    {t | ∃ j < nA (hsrc x.base.jobs x.base.machines (recN x R) (objN x) Z sg ab),
      fullH (hsrc x.base.jobs x.base.machines (recN x R) (objN x) Z sg ab) j = t} = typeTuples x := by
  have hO : ∀ j < x.base.jobs, (objN x j).length = 3 := fun j hj => objN_length x hj
  have hcard : ∀ j : Fin x.base.jobs, Nat.card {j' // Record x j' (R j) ∧ objOf x j' = objOf x j} =
      cntH (hsrc x.base.jobs x.base.machines (recN x R) (objN x) Z sg ab) j.val := by
    intro j
    rw [cntH_hsrc x.base.machines (recN x R) Z sg ab hO j.isLt]
    refine natCard_eq_filter _ _ fun i hi => ?_
    simp only [decide_eq_true_eq, recN, objN, dif_pos hi, dif_pos j.isLt, record_iff hR]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj' h (by simp [objOf])
      exact ⟨h1.symm, h2⟩
    · rintro ⟨h1, h2⟩
      show R ⟨i, hi⟩ ++ objOf x ⟨i, hi⟩ = R j ++ objOf x j
      rw [← h1, h2]
  ext t
  simp only [Set.mem_ofPred_eq, typeTuples, nA_hsrc x.base.machines (recN x R) Z sg ab hO]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨R ⟨j, hj⟩, ⟨j, hj⟩, hR _, ?_⟩
    rw [fullH, hcard, tupH_hsrc x.base.machines (recN x R) Z sg ab hO hj]
    simp [recN, objN, hj]
  · rintro ⟨b, j, hb, rfl⟩
    rw [(record_iff hR j b).mp hb]
    refine ⟨j.val, j.isLt, ?_⟩
    rw [fullH, hcard, tupH_hsrc x.base.machines (recN x R) Z sg ab hO j.isLt]
    simp [recN, objN]

variable {t : Spec OperationsFamily.family}

/-- **The image of the standard word of an instance without facts on pairs of jobs is a
high-multiplicity word of its lift.** -/
theorem hmWord_encodes (hle : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .highMultiplicity) {x : Inst OperationsFamily.family s}
    (hp : pairTuples x = ∅) {u : List ℕ} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at s) u x D) :
    EncodesDecision (StandardReading.ops.at t) (hmWord u)
      ((Assembly.lift _ OperationsFamily.family_sound hle).map x) D := by
  obtain ⟨R, b₂, b₃, hR, hb₂, hb₃, rfl⟩ := word_std x hs hx
  have hO : ∀ j < x.base.jobs, (objN x j).length = 3 := fun j hj => objN_length x hj
  have hL : Lists (typeTuples ((Assembly.lift _ OperationsFamily.family_sound hle).map x))
      (typesH (hsrc x.base.jobs x.base.machines (recN x R) (objN x) (b₂ ++ b₃)
        (if D < 0 then 1 else 0) D.natAbs)) := by
    rw [Lax434175Proofs.PropagationStandard.typeTuples_up, ← typeTuples_hsrc hR]
    exact typesH_lists _
  refine ⟨[1, x.base.jobs, x.base.machines] ++ flat (typesH (hsrc x.base.jobs x.base.machines
    (recN x R) (objN x) (b₂ ++ b₃) (if D < 0 then 1 else 0) D.natAbs)) ++ b₂ ++ b₃, ?_, b₂, b₃, ?_, ?_,
    Or.inr ⟨ht, ?_, _, ⟨_, hL, rfl⟩, rfl⟩⟩
  · rw [hmWord_hsrc x.base.machines (recN x R) (b₂ ++ b₃) _ _ hO]; simp
  · rwa [Lax434175Proofs.PropagationStandard.pairTuples_up]
  · rwa [Lax434175Proofs.PropagationStandard.globalTuples_up]
  · rwa [Lax434175Proofs.PropagationStandard.pairTuples_up]

end Inst

/-! ### Two instances of one high-multiplicity word -/

section Pair
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175Proofs.StandardParse

theorem block_exists {S : Set (List ℕ)} (hS : S.Finite) : ∃ b, Block S b :=
  ⟨flat (hS.toFinset.sort (· ≤ ·)), _, ⟨(Finset.sortedLT_sort _).pairwise, fun t => by simp⟩, rfl⟩

variable {t : Spec OperationsFamily.family}

/-- **Every job has a record**: its three sets of tuples are finite. -/
theorem record_exists (y : Inst OperationsFamily.family t) (j : Fin y.base.jobs) :
    ∃ b, Record y j b := by
  have h₁ : (machineTuples y j).Finite :=
    (Set.finite_range fun a : Fin (y.base.ops j) × Finset (Fin y.base.machines) =>
      a.1.val :: machinesWord a.2).subset fun _ ⟨k, S, _, h⟩ => ⟨(k, S), h.symm⟩
  have h₂ : (serverTuples y j).Finite := by
    refine (Set.finite_range fun k : Fin (y.base.ops j) =>
      [k.val, ((Servers.view (t.module .server)
        (y.data .server : Servers.Data (Operations.Op y.base) _)).getD fun _ => 0) ⟨j, k⟩]).subset ?_
    rintro _ ⟨k, f, hf, rfl⟩
    exact ⟨k, by rw [hf]; rfl⟩
  have h₃ : (transportTuples y j).Finite :=
    (Set.finite_range fun a : Fin (y.base.ops j) × Fin (y.base.ops j) =>
      [a.1.val, a.2.val, (y.data .transportation : Transportation.Data y.base.toShop).1 j a.1 a.2]).subset
      fun _ ⟨k, k', h⟩ => ⟨(k, k'), h.symm⟩
  obtain ⟨b₁, hb₁⟩ := block_exists h₁
  obtain ⟨b₂, hb₂⟩ := block_exists h₂
  obtain ⟨b₃, hb₃⟩ := block_exists h₃
  exact ⟨_, b₁, b₂, b₃, hb₁, hb₂, hb₃, rfl⟩

/-- **The parse of a high-multiplicity word**: the number of machines and the type tuples. -/
theorem hm_parse (ht : t.module .encoding = .highMultiplicity) {y y' : Inst OperationsFamily.family t}
    {z : List ℕ} (hz : EncodesOps y z) (hz' : EncodesOps y' z) :
    y.base.machines = y'.base.machines ∧ typeTuples y = typeTuples y' := by
  obtain ⟨b₂, b₃, hb₂, hb₃, ⟨hst, -⟩ | ⟨-, -, b₁, hb₁, rfl⟩⟩ := hz
  · exact ForbiddenTimes.Encoding.noConfusion (ht.symm.trans hst)
  obtain ⟨b₂', b₃', hb₂', hb₃', ⟨hst, -⟩ | ⟨-, -, b₁', hb₁', e⟩⟩ := hz'
  · exact ForbiddenTimes.Encoding.noConfusion (ht.symm.trans hst)
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and, List.append_assoc] at e
  obtain ⟨-, hm, e⟩ := e
  exact ⟨hm, (block_prefix hb₁ hb₁' e).1⟩

theorem ptimes_cast {o o' m m' : ℕ} {q : Fin o → Fin m → ℕ} {q' : Fin o' → Fin m' → ℕ} (ho : o = o')
    (hm : m = m') (hP : (List.ofFn fun k => List.ofFn fun i => q k i).flatten =
      (List.ofFn fun k => List.ofFn fun i => q' k i).flatten) :
    ∀ k i, q' (Fin.cast ho k) (Fin.cast hm i) = q k i := by
  subst ho; subst hm
  obtain rfl := ptimes_inj hP
  intro k i; rfl

/-- **Jobs with one record have the same processing times.** -/
theorem opTime_of_record {y y' : Inst OperationsFamily.family t} (hm : y.base.machines = y'.base.machines)
    {j : Fin y.base.jobs} {j' : Fin y'.base.jobs} {b : List ℕ} (h : Record y j b) (h' : Record y' j' b)
    (k : Fin (y.base.ops j)) :
    ∃ k' : Fin (y'.base.ops j'), Operations.opTime y'.base ⟨j', k'⟩ = Operations.opTime y.base ⟨j, k⟩ := by
  obtain ⟨b₁, b₂, b₃, -, -, -, hb⟩ := Lax434175Proofs.Determined.record_split y j h
  obtain ⟨c₁, c₂, c₃, -, -, -, hc⟩ := Lax434175Proofs.Determined.record_split y' j' h'
  have e := hb.symm.trans hc
  simp only [List.singleton_append, List.cons.injEq] at e
  obtain ⟨ho, e⟩ := e
  obtain ⟨hP, -⟩ := fixed_prefix (by rw [ptimes_length, ptimes_length, ho, hm]) e
  have hq := ptimes_cast ho hm hP
  refine ⟨Fin.cast ho k, ?_⟩
  unfold Operations.opTime
  by_cases h0 : 0 < y.base.machines
  · rw [dif_pos h0, dif_pos (hm ▸ h0)]
    exact hq k ⟨0, h0⟩
  · rw [dif_neg h0, dif_neg (hm ▸ h0)]

/-- **Two instances of one high-multiplicity word**: the processing times of the operations of
the first are processing times of the second. -/
theorem numP_le (ht : t.module .encoding = .highMultiplicity) {y y' : Inst OperationsFamily.family t}
    {z : List ℕ} (hz : EncodesOps y z) (hz' : EncodesOps y' z) :
    ResultParameters.Ops.numP t y ≤ ResultParameters.Ops.numP t y' := by
  obtain ⟨hm, hT⟩ := hm_parse ht hz hz'
  unfold ResultParameters.Ops.numP
  refine Finset.card_le_card fun v hv => ?_
  obtain ⟨⟨j, k⟩, -, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨b, hb⟩ := record_exists y j
  have hmem : (Nat.card {j' // Record y j' b ∧ objOf y j' = objOf y j} :: (b ++ objOf y j)) ∈
      typeTuples y := ⟨b, j, hb, rfl⟩
  rw [hT] at hmem
  obtain ⟨b', j', hb', he⟩ := hmem
  obtain ⟨hbb, -⟩ := List.append_inj' (List.cons.inj he).2 (by simp [objOf])
  rw [hbb] at hb
  obtain ⟨k', hk'⟩ := opTime_of_record hm hb hb' k
  exact Finset.mem_image.mpr ⟨⟨j', k'⟩, Finset.mem_univ _, hk'⟩

end Pair

end Lax434175Proofs.HighMultiplicityWords
