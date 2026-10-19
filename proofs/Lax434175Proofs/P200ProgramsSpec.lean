import Mathlib.Tactic
import Lax434175Proofs.P200Raw
import Lax434175Proofs.IsemWords

/-!
The word map from the standard words of `P|M_j|Σ w_j Z_j` (`stdWordR`) to the words of
interval scheduling of the scaled instance (`Points.Raw.toIsem`), as functions on all words.

* `parseWord` reads the standard word: the number of jobs and machines, the threshold
  `(Σ w_j - D)⁺`, then the processing times, the due dates, the weights and the machines of
  the jobs, in the compressed form of interval scheduling (offsets and targets). When a job
  has no machine it writes `[0, 0, 1]`.
* `buildWord` writes the scaled instance from that word.

Every loop bound is capped by the length of the word, so both maps are polynomial on every
word; on the words of instances the caps change nothing.
-/

namespace Lax434175Proofs.P200Programs
open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175Proofs.Points Lax434175Proofs.P200Raw

/-! ### Lists -/

/-- The sum of the first `j` values. -/
def psum (f : ℕ → ℕ) (j : ℕ) : ℕ := ((List.range j).map f).sum

@[simp] theorem psum_zero (f : ℕ → ℕ) : psum f 0 = 0 := rfl

theorem psum_succ (f : ℕ → ℕ) (j : ℕ) : psum f (j + 1) = psum f j + f j := by
  unfold psum; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem psum_mono (f : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : psum f i ≤ psum f j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.of_le_succ h with h | h
    · rw [psum_succ]; exact (ih h).trans (Nat.le_add_right _ _)
    · rw [h]

theorem psum_congr {f g : ℕ → ℕ} {j : ℕ} (h : ∀ k < j, f k = g k) : psum f j = psum g j := by
  unfold psum
  rw [List.map_congr_left fun k hk => h k (List.mem_range.mp hk)]

theorem psum_le_mul (f : ℕ → ℕ) {c : ℕ} (hc : ∀ k, f k ≤ c) (j : ℕ) : psum f j ≤ j * c := by
  induction j with
  | zero => simp
  | succ j ih => rw [psum_succ, Nat.succ_mul]; have := hc j; omega

theorem psum_const (c j : ℕ) : psum (fun _ => c) j = c * j := by
  induction j with
  | zero => simp
  | succ j ih => rw [psum_succ, ih]; ring

theorem length_flatMap_range (g : ℕ → List ℕ) (n : ℕ) :
    ((List.range n).flatMap g).length = psum (fun k => (g k).length) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih, psum_succ]; simp

theorem gA {l l' : List ℕ} {k : ℕ} :
    (l ++ l').getD k 0 = if k < l.length then l.getD k 0 else l'.getD (k - l.length) 0 := by
  split_ifs with h
  · exact List.getD_append _ _ _ _ h
  · exact List.getD_append_right _ _ _ _ (by omega)

theorem getD_flatMap_range (g : ℕ → List ℕ) {n j t : ℕ} (hj : j < n) (ht : t < (g j).length) :
    ((List.range n).flatMap g).getD (psum (fun k => (g k).length) j + t) 0 = (g j).getD t 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, gA, length_flatMap_range]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · have := psum_mono (fun k => (g k).length) (show j + 1 ≤ n by omega)
      rw [psum_succ] at this
      rw [if_pos (by omega)]
      exact ih h
    · subst h
      rw [if_neg (by omega)]
      simp

theorem getD_map_range {g : ℕ → ℕ} {k n : ℕ} (hk : k < n) : ((List.range n).map g).getD k 0 = g k := by
  rw [List.getD_eq_getElem?_getD]; simp [hk]

theorem map_range_getD (l : List ℕ) : (List.range l.length).map (fun t => l.getD t 0) = l :=
  (Lax434175Proofs.ThresholdProgram.map_range_getD l le_rfl).trans List.take_length

theorem getD_triples (l : List ℕ) (a b : ℕ) {t : ℕ} (ht : t < l.length) :
    (l.flatMap fun i => [a, b, i]).getD (3 * t + 2) 0 = l.getD t 0 := by
  induction l generalizing t with
  | nil => simp at ht
  | cons x l ih =>
    rcases t with _ | t
    · simp
    · rw [List.flatMap_cons, gA, if_neg (by simp; omega)]
      simp only [List.length_cons, List.length_nil, List.getD_cons_succ]
      rw [show 3 * (t + 1) + 2 - (0 + 1 + 1 + 1) = 3 * t + 2 by omega]
      exact ih (by simp at ht; omega)

theorem length_filter_range (q : ℕ → Bool) (j : ℕ) :
    ((List.range j).filter q).length = psum (fun k => if q k then 1 else 0) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, psum_succ]
    by_cases h : q j <;> simp [h]

/-! ### Reading the standard word -/

/-- The number of jobs, capped by the length. -/
def nA (u : List ℕ) : ℕ := min (u.getD 1 0) u.length

/-- The number of machines. -/
def mA (u : List ℕ) : ℕ := u.getD 2 0

/-- Where the record of job `j` begins (at its length). -/
def posA (u : List ℕ) : ℕ → ℕ
  | 0 => 3
  | j + 1 => posA u j + 1 + u.getD (posA u j) 0

/-- The processing time of job `j`: the first entry of its times. -/
def pA (u : List ℕ) (j : ℕ) : ℕ := u.getD (posA u j + 2) 0

/-- The number of machines of job `j`. -/
def cntA (u : List ℕ) (j : ℕ) : ℕ := u.getD (posA u j + mA u + 3) 0

/-- The number of machines of job `j`, capped by the length. -/
def cA (u : List ℕ) (j : ℕ) : ℕ := min (cntA u j) u.length

/-- The `t`-th machine of job `j`. -/
def mchA (u : List ℕ) (j t : ℕ) : ℕ := u.getD (posA u j + mA u + 6 + 3 * t) 0

/-- Where the objective triples begin. -/
def objA (u : List ℕ) : ℕ := posA u (nA u) + 7

def wA (u : List ℕ) (j : ℕ) : ℕ := u.getD (objA u + 3 * j + 1) 0

def dA (u : List ℕ) (j : ℕ) : ℕ := u.getD (objA u + 3 * j + 2) 0

/-- The total weight. -/
def totA (u : List ℕ) : ℕ := psum (wA u) (nA u)

/-- The threshold `(Σ w_j - D)⁺`, from the sign and the absolute value of `D` at the end. -/
def WA (u : List ℕ) : ℕ :=
  if u.getD (u.length - 2) 0 = 0 then totA u - u.getD (u.length - 1) 0
  else totA u + u.getD (u.length - 1) 0

/-- The offsets. -/
def offA (u : List ℕ) (i : ℕ) : ℕ := psum (cA u) i

/-- Some job has no machine. -/
def badA (u : List ℕ) : Bool := (List.range (nA u)).any fun j => cntA u j == 0

/-- **The parsed word.** -/
def parseWord (u : List ℕ) : List ℕ :=
  if badA u then [0, 0, 1] else
  [nA u, mA u, WA u] ++ (List.range (nA u)).map (pA u) ++ (List.range (nA u)).map (dA u) ++
    (List.range (nA u)).map (wA u) ++ (List.range (nA u + 1)).map (offA u) ++
    (List.range (nA u)).flatMap fun j => (List.range (cA u j)).map (mchA u j)

/-! ### Writing the scaled instance -/

section Build
variable (x : List ℕ)

def nB : ℕ := min (x.getD 0 0) x.length
def mB : ℕ := x.getD 1 0
def WB : ℕ := x.getD 2 0
def pB (j : ℕ) : ℕ := x.getD (3 + j) 0
def dB (j : ℕ) : ℕ := x.getD (3 + nB x + j) 0
def wB (j : ℕ) : ℕ := x.getD (3 + 2 * nB x + j) 0
def oB (i : ℕ) : ℕ := x.getD (3 + 3 * nB x + i) 0
def tB (q : ℕ) : ℕ := x.getD (4 + 4 * nB x + q) 0
/-- The number of machines of job `j`, capped by the length. -/
def cB (j : ℕ) : ℕ := min (oB x (j + 1) - oB x j) x.length

/-- Job `k` is a point with the due date and the machines of job `j`. -/
def sameB (j k : ℕ) : Bool :=
  pB x k == 0 && dB x k == dB x j && cB x j == cB x k &&
    (List.range (cB x j)).all fun t => tB x (oB x j + t) == tB x (oB x k + t)

/-- The first point of its kind. -/
def headB (j : ℕ) : Bool := pB x j == 0 && !((List.range j).any fun k => sameB x j k)

/-- A job of positive length that can be on time. -/
def realB (j : ℕ) : Bool := decide (0 < pB x j) && decide (pB x j ≤ dB x j)

def keepB (j : ℕ) : Bool := realB x j || headB x j

def rB : ℕ := min (2 ^ min (mB x) (nB x)) (nB x)

def KB : ℕ := 2 * rB x + 3

def slotB (j : ℕ) : ℕ := ((List.range j).filter fun k => headB x k && dB x k == dB x j).length

def pOut (j : ℕ) : ℕ := if realB x j then KB x * pB x j - 2 * rB x - 2 else 1

def dOut (j : ℕ) : ℕ :=
  if realB x j then KB x * dB x j - rB x - 1
  else if headB x j then KB x * dB x j + slotB x j + 1 else 1

/-- The weight of a head: all the points of its kind. -/
def hwB (j : ℕ) : ℕ := psum (fun k => if sameB x j k then wB x k else 0) (nB x)

def wOut (j : ℕ) : ℕ := if realB x j then wB x j else if headB x j then hwB x j else 0

def tgOut (j : ℕ) : List ℕ :=
  if keepB x j then (List.range (cB x j)).map (fun t => tB x (oB x j + t)) else [mB x]

/-- The machines of the padded instance: one more, except on the short word of a no-instance. -/
def mOut : ℕ := if x.length < 4 then mB x else mB x + 1

def offOut (i : ℕ) : ℕ := psum (fun j => (tgOut x j).length) i

/-- **The word of the scaled instance.** -/
def buildWord : List ℕ :=
  [nB x, mOut x] ++ (List.range (nB x)).map (pOut x) ++ (List.range (nB x)).map (dOut x) ++
    (List.range (nB x)).map (wOut x) ++ (List.range (nB x + 1)).map (offOut x) ++
    (List.range (nB x)).flatMap (tgOut x) ++ [WB x]

end Build

/-- **The word map.** -/
def toIsemWord (u : List ℕ) : List ℕ := buildWord (parseWord u)

theorem buildWord_bad : buildWord [0, 0, 1] = [0, 0, 0, 1] := by decide


/-! ### Words of a fixed layout -/

theorem getD_app (l l' : List ℕ) (k : ℕ) : (l ++ l').getD (l.length + k) 0 = l'.getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem getD_mem {l : List ℕ} {s : ℕ} (h : s < l.length) : l.getD s 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem eq_of_getD {l₁ l₂ : List ℕ} (hl : l₁.length = l₂.length)
    (h : ∀ t < l₁.length, l₁.getD t 0 = l₂.getD t 0) : l₁ = l₂ := by
  rw [← map_range_getD l₁, ← map_range_getD l₂, ← hl]
  exact List.map_congr_left fun t ht => h t (List.mem_range.mp ht)

theorem psum_ge (f : ℕ → ℕ) {c j : ℕ} (hc : ∀ k < j, c ≤ f k) : j * c ≤ psum f j := by
  induction j with
  | zero => simp
  | succ j ih => rw [psum_succ, Nat.succ_mul]; have := hc j (by omega); have := ih fun k hk => hc k (by omega); omega

theorem psum_eq_of_zero (f : ℕ → ℕ) {j n : ℕ} (hjn : j ≤ n) (h : ∀ k, j ≤ k → k < n → f k = 0) :
    psum f n = psum f j := by
  induction n with
  | zero => rw [Nat.le_zero.mp hjn]
  | succ n ih =>
    rcases Nat.of_le_succ hjn with h1 | h1
    · rw [psum_succ, h n h1 (by omega), ih h1 fun k hk1 hk2 => h k hk1 (by omega)]; rfl
    · rw [h1]

/-- Every position below the last offset lies in some block. -/
theorem psum_cover (f : ℕ → ℕ) {n t : ℕ} (ht : t < psum f n) :
    ∃ j < n, psum f j ≤ t ∧ t < psum f (j + 1) := by
  induction n with
  | zero => simp at ht
  | succ n ih =>
    by_cases h : t < psum f n
    · obtain ⟨j, hj, h1, h2⟩ := ih h; exact ⟨j, by omega, h1, h2⟩
    · exact ⟨n, by omega, by omega, ht⟩

/-- A header, three arrays of `n` numbers, `n + 1` offsets and the blocks they cut. -/
def lay (hd : List ℕ) (n : ℕ) (P Dd Ww : ℕ → ℕ) (T : ℕ → List ℕ) : List ℕ :=
  hd ++ ((List.range n).map P ++ ((List.range n).map Dd ++ ((List.range n).map Ww ++
    ((List.range (n + 1)).map (psum fun j => (T j).length) ++ (List.range n).flatMap T))))

section Lay
variable (hd : List ℕ) (n : ℕ) (P Dd Ww : ℕ → ℕ) (T : ℕ → List ℕ)

theorem lay_length :
    (lay hd n P Dd Ww T).length = hd.length + 4 * n + 1 + psum (fun j => (T j).length) n := by
  simp only [lay, List.length_append, List.length_map, List.length_range, length_flatMap_range]; omega

theorem lay_hd {k : ℕ} (hk : k < hd.length) : (lay hd n P Dd Ww T).getD k 0 = hd.getD k 0 :=
  List.getD_append _ _ _ _ hk

theorem lay_P {j : ℕ} (hj : j < n) : (lay hd n P Dd Ww T).getD (hd.length + j) 0 = P j := by
  rw [lay, getD_app, List.getD_append _ _ _ _ (by simpa using hj), getD_map_range hj]

theorem lay_D {j : ℕ} (hj : j < n) : (lay hd n P Dd Ww T).getD (hd.length + n + j) 0 = Dd j := by
  rw [lay, show hd.length + n + j = hd.length + (((List.range n).map P).length + j) by simp; omega,
    getD_app, getD_app, List.getD_append _ _ _ _ (by simpa using hj), getD_map_range hj]

theorem lay_W {j : ℕ} (hj : j < n) : (lay hd n P Dd Ww T).getD (hd.length + 2 * n + j) 0 = Ww j := by
  rw [lay, show hd.length + 2 * n + j = hd.length + (((List.range n).map P).length +
    (((List.range n).map Dd).length + j)) by simp; omega,
    getD_app, getD_app, getD_app, List.getD_append _ _ _ _ (by simpa using hj), getD_map_range hj]

theorem lay_O {i : ℕ} (hi : i ≤ n) :
    (lay hd n P Dd Ww T).getD (hd.length + 3 * n + i) 0 = psum (fun j => (T j).length) i := by
  rw [lay, show hd.length + 3 * n + i = hd.length + (((List.range n).map P).length +
    (((List.range n).map Dd).length + (((List.range n).map Ww).length + i))) by simp; omega,
    getD_app, getD_app, getD_app, getD_app, List.getD_append _ _ _ _ (by simp; omega),
    getD_map_range (by omega)]

theorem lay_T (t : ℕ) :
    (lay hd n P Dd Ww T).getD (hd.length + 4 * n + 1 + t) 0 = ((List.range n).flatMap T).getD t 0 := by
  rw [lay, show hd.length + 4 * n + 1 + t = hd.length + (((List.range n).map P).length +
    (((List.range n).map Dd).length + (((List.range n).map Ww).length +
    (((List.range (n + 1)).map (psum fun j => (T j).length)).length + t)))) by simp; omega,
    getD_app, getD_app, getD_app, getD_app, getD_app]

end Lay

/-- **The words of the layout with header `[n, m]` encode instances.** -/
theorem encodes_lay (I : Instance) (P Dd Ww : ℕ → ℕ) (T : ℕ → List ℕ)
    (hP : ∀ j : Fin I.jobs, P j = I.p j) (hD : ∀ j : Fin I.jobs, Dd j = I.d j)
    (hW : ∀ j : Fin I.jobs, Ww j = I.w j) (hT : ∀ j < I.jobs, ∀ v ∈ T j, v < I.machines)
    (hE : ∀ (j : Fin I.jobs) (i : Fin I.machines), i ∈ I.eligible j ↔ i.val ∈ T j) :
    EncodesInstance (lay [I.jobs, I.machines] I.jobs P Dd Ww T) I := by
  set n := I.jobs
  set S := psum fun j => (T j).length with hS
  set y := lay [I.jobs, I.machines] I.jobs P Dd Ww T
  have hjc : jobCount y = n := lay_hd _ _ _ _ _ _ (k := 0) (by simp)
  have hoff : ∀ i ≤ n, offset y i = S i := by
    intro i hi
    unfold offset; rw [hjc]
    exact lay_O [I.jobs, I.machines] n P Dd Ww T hi
  have htg : ∀ t, target y t = ((List.range n).flatMap T).getD t 0 := by
    intro t
    unfold target; rw [hjc, show 3 + 4 * n + t = [I.jobs, I.machines].length + 4 * n + 1 + t by
      simp only [List.length_cons, List.length_nil]; omega]
    exact lay_T [I.jobs, I.machines] n P Dd Ww T t
  have hblk : ∀ j < n, ∀ s < (T j).length, target y (S j + s) = (T j).getD s 0 := by
    intro j hj s hs
    rw [htg]; exact getD_flatMap_range T hj hs
  have hS1 : ∀ j, S (j + 1) = S j + (T j).length := fun j => psum_succ _ j
  refine ⟨hjc, lay_hd _ _ _ _ _ _ (k := 1) (by simp), ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_,
    fun j hj => ?_, fun t ht => ?_, fun j i => ?_⟩
  · have e : S I.jobs = S n := rfl
    rw [hoff n le_rfl, lay_length, ← hS]; simp only [List.length_cons, List.length_nil]; omega
  · rw [← hP j]; exact lay_P [I.jobs, I.machines] n P Dd Ww T j.isLt
  · rw [← hD j]; unfold due; rw [hjc]; exact lay_D [I.jobs, I.machines] n P Dd Ww T j.isLt
  · rw [← hW j]; unfold wt; rw [hjc]; exact lay_W [I.jobs, I.machines] n P Dd Ww T j.isLt
  · rw [hoff 0 (Nat.zero_le _)]; rfl
  · rw [hoff j hj.le, hoff (j + 1) hj, hS1]; omega
  · rw [hoff n le_rfl] at ht
    obtain ⟨j, hj, h1, h2⟩ := psum_cover _ ht
    rw [← hS] at h1 h2
    rw [hS1] at h2
    rw [show t = S j + (t - S j) by omega, hblk j hj _ (by omega)]
    exact hT j hj _ (getD_mem (by omega))
  · rw [hE, hoff j j.isLt.le, hoff (j + 1) j.isLt, hS1]
    constructor
    · intro hi
      obtain ⟨s, hs, he⟩ := List.mem_iff_getElem.mp hi
      refine ⟨S j + s, by omega, by omega, ?_⟩
      rw [hblk j j.isLt s hs, List.getD_eq_getElem _ _ hs, he]
    · rintro ⟨t, h1, h2, he⟩
      rw [show t = S j + (t - S j) by omega, hblk j j.isLt _ (by omega)] at he
      rw [← he]; exact getD_mem (by omega)

/-! ### The data of the standard word -/

section RawWord
variable (R : Raw)

/-- The machines of a job, increasing. -/
def mlR (j : Fin R.jobs) : List ℕ :=
  (List.range R.machines).filter fun i =>
    if h : i < R.machines then decide ((⟨i, h⟩ : Fin R.machines) ∈ R.elig j) else false

theorem machListR_eq (j : Fin R.jobs) : machListR R j = (mlR R j).map fun i => [0, i] := rfl

theorem mem_mlR (j : Fin R.jobs) (i : Fin R.machines) : i.val ∈ mlR R j ↔ i ∈ R.elig j := by
  unfold mlR
  simp only [List.mem_filter, List.mem_range, dif_pos i.isLt, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨i.isLt, h⟩⟩

theorem lt_of_mem_mlR {j : Fin R.jobs} {v : ℕ} (h : v ∈ mlR R j) : v < R.machines := by
  unfold mlR at h; exact List.mem_range.mp (List.mem_filter.mp h).1

theorem mlR_eq_iff (j k : Fin R.jobs) : mlR R j = mlR R k ↔ R.elig j = R.elig k := by
  constructor
  · intro h; ext i; rw [← mem_mlR, ← mem_mlR, h]
  · intro h; unfold mlR; rw [h]

theorem mlR_nil_iff (j : Fin R.jobs) : mlR R j = [] ↔ ¬ (R.elig j).Nonempty := by
  rw [List.eq_nil_iff_forall_not_mem, Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h i hi; exact h _ ((mem_mlR R j i).mpr hi)
  · intro h v hv; exact h ⟨v, lt_of_mem_mlR R hv⟩ ((mem_mlR R j ⟨v, lt_of_mem_mlR R hv⟩).mp hv)

def blkN (j : ℕ) : List ℕ := if h : j < R.jobs then (recR R ⟨j, h⟩).length :: recR R ⟨j, h⟩ else []
def objN (j : ℕ) : List ℕ := if h : j < R.jobs then [0, R.w ⟨j, h⟩, R.d ⟨j, h⟩] else []
def mlN (j : ℕ) : List ℕ := if h : j < R.jobs then mlR R ⟨j, h⟩ else []
def pR (j : ℕ) : ℕ := if h : j < R.jobs then R.p ⟨j, h⟩ else 0
def dR (j : ℕ) : ℕ := if h : j < R.jobs then R.d ⟨j, h⟩ else 0
def wR (j : ℕ) : ℕ := if h : j < R.jobs then R.w ⟨j, h⟩ else 0

theorem stdWordR_eq (D : ℤ) : stdWordR R D = [0, R.jobs, R.machines] ++
    ((List.range R.jobs).flatMap (blkN R) ++ ([0] ++ ((if R.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) ++
      ((List.range R.jobs).flatMap (objN R) ++ Lax434175.StandardReading.int D)))) := by
  unfold stdWordR stdInstR
  rw [IsemWords.ofFn_eq_range, IsemWords.ofFn_eq_range]
  simp only [List.append_assoc]
  rfl

theorem blk_eq (j : Fin R.jobs) : blkN R j = ([(recR R j).length, 1] ++ List.replicate R.machines (R.p j) ++
    [0, (mlR R j).length]) ++ ((mlR R j).flatMap (fun i => [2, 0, i]) ++ [0, 1, 3, 0, 0, 0, 0]) := by
  simp [blkN, recR, Lax434175.StandardReading.flat, machListR_eq, List.flatMap_map]

theorem blk_length (j : Fin R.jobs) : (blkN R j).length = R.machines + 3 * (mlR R j).length + 11 := by
  rw [blk_eq]
  have : ((mlR R j).flatMap (fun i => [2, 0, i])).length = 3 * (mlR R j).length := by
    rw [List.length_flatMap]; simp [mul_comm]
  simp only [List.length_append, this, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem objN_length {j : ℕ} (hj : j < R.jobs) : (objN R j).length = 3 := by simp [objN, hj]

variable (D : ℤ)

/-- The start of the record of job `j`. -/
abbrev bpos (j : ℕ) : ℕ := 3 + psum (fun k => (blkN R k).length) j

theorem getD_blk {j q : ℕ} (hj : j < R.jobs) (hq : q < (blkN R j).length) :
    (stdWordR R D).getD (bpos R j + q) 0 = (blkN R j).getD q 0 := by
  have h1 := psum_mono (fun k => (blkN R k).length) (show j + 1 ≤ R.jobs by omega)
  rw [psum_succ] at h1
  rw [stdWordR_eq, show bpos R j + q = [0, R.jobs, R.machines].length +
    (psum (fun k => (blkN R k).length) j + q) by simp only [bpos, List.length_cons, List.length_nil]; omega,
    getD_app, List.getD_append _ _ _ _ (by rw [length_flatMap_range]; omega), getD_flatMap_range _ hj hq]

theorem posA_eq : ∀ j ≤ R.jobs, posA (stdWordR R D) j = bpos R j
  | 0, _ => rfl
  | j + 1, hj => by
    have hl := blk_length R ⟨j, by omega⟩
    have hb : blkN R j = (recR R ⟨j, by omega⟩).length :: recR R ⟨j, by omega⟩ := by simp [blkN, show j < R.jobs by omega]
    rw [posA, posA_eq j (by omega), show bpos R j = bpos R j + 0 from rfl,
      getD_blk R D (by omega) (by simp [hb]), bpos, bpos, psum_succ]
    simp [hb]; omega

theorem length_stdWordR :
    (stdWordR R D).length = 3 + psum (fun k => (blkN R k).length) R.jobs + 1 +
      (if R.jobs = 0 then 1 else 6) + 3 * R.jobs + 2 := by
  rw [stdWordR_eq]
  have : psum (fun k => (objN R k).length) R.jobs = 3 * R.jobs := by
    rw [psum_congr (g := fun _ => 3) fun k hk => objN_length R hk, psum_const]
  simp only [List.length_append, List.length_cons, List.length_nil, length_flatMap_range, this]
  split_ifs <;> simp [Lax434175.StandardReading.int] <;> omega

theorem nA_eq : nA (stdWordR R D) = R.jobs := by
  unfold nA
  have : (stdWordR R D).getD 1 0 = R.jobs := by rw [stdWordR_eq]; rfl
  rw [this, length_stdWordR]; omega

theorem mA_eq : mA (stdWordR R D) = R.machines := by unfold mA; rw [stdWordR_eq]; rfl

theorem pA_eq (hm : 0 < R.machines) (j : Fin R.jobs) : pA (stdWordR R D) j = R.p j := by
  unfold pA
  rw [posA_eq R D j j.isLt.le, getD_blk R D j.isLt (by rw [blk_length]; omega), blk_eq]
  rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp; omega),
    show 2 = [(recR R j).length, 1].length + 0 from rfl, getD_app, List.getD_eq_getElem?_getD]
  simp [hm]

theorem cntA_eq (j : Fin R.jobs) : cntA (stdWordR R D) j = (mlR R j).length := by
  unfold cntA
  rw [posA_eq R D j j.isLt.le, mA_eq, add_assoc, getD_blk R D j.isLt (by rw [blk_length]; omega), blk_eq,
    List.getD_append _ _ _ _ (by simp),
    show R.machines + 3 = ([(recR R j).length, 1] ++ List.replicate R.machines (R.p j)).length + 1 by
      simp,
    getD_app]
  rfl

theorem mchA_eq (j : Fin R.jobs) {t : ℕ} (ht : t < (mlR R j).length) :
    mchA (stdWordR R D) j t = (mlR R j).getD t 0 := by
  have hT : ((mlR R j).flatMap (fun i => [2, 0, i])).length = 3 * (mlR R j).length := by
    rw [List.length_flatMap]; simp [mul_comm]
  unfold mchA
  rw [posA_eq R D j j.isLt.le, mA_eq, show bpos R j + R.machines + 6 + 3 * t =
    bpos R j + (R.machines + 6 + 3 * t) by omega, getD_blk R D j.isLt (by rw [blk_length]; omega), blk_eq,
    show R.machines + 6 + 3 * t = ([(recR R j).length, 1] ++ List.replicate R.machines (R.p j) ++
      [0, (mlR R j).length]).length + (3 * t + 2) by simp; omega,
    getD_app, List.getD_append _ _ _ _ (by rw [hT]; omega), getD_triples _ _ _ ht]

theorem obj_getD (hn : 0 < R.jobs) {j r : ℕ} (hj : j < R.jobs) (hr : r < 3) :
    (stdWordR R D).getD (objA (stdWordR R D) + 3 * j + r) 0 = (objN R j).getD r 0 := by
  have h3 : psum (fun k => (objN R k).length) j = 3 * j := by
    rw [psum_congr (g := fun _ => 3) fun k hk => objN_length R (by omega), psum_const]
  unfold objA
  rw [nA_eq, posA_eq R D _ le_rfl, stdWordR_eq, if_neg (by omega),
    show bpos R R.jobs + 7 + 3 * j + r = [0, R.jobs, R.machines].length +
      (((List.range R.jobs).flatMap (blkN R)).length + ([0].length + ([1, 4, 1, 0, 0, 0].length +
        (psum (fun k => (objN R k).length) j + r)))) by
      rw [length_flatMap_range, h3]; simp only [bpos, List.length_cons, List.length_nil]; omega,
    getD_app, getD_app, getD_app, getD_app, List.getD_append _ _ _ _ ?_,
    getD_flatMap_range _ hj (by rw [objN_length R hj]; exact hr)]
  rw [length_flatMap_range]
  have := psum_mono (fun k => (objN R k).length) (show j + 1 ≤ R.jobs by omega)
  rw [psum_succ, objN_length R hj] at this
  omega

theorem wA_eq (hn : 0 < R.jobs) (j : Fin R.jobs) : wA (stdWordR R D) j = R.w j := by
  unfold wA; rw [obj_getD R D hn j.isLt (by norm_num)]; simp [objN]

theorem dA_eq (hn : 0 < R.jobs) (j : Fin R.jobs) : dA (stdWordR R D) j = R.d j := by
  unfold dA; rw [obj_getD R D hn j.isLt (by norm_num)]; simp [objN]

theorem totA_eq : totA (stdWordR R D) = R.total := by
  unfold totA Raw.total
  rw [nA_eq, psum_congr (g := wR R) fun k hk => by rw [wA_eq R D (by omega) ⟨k, hk⟩]; simp [wR, hk]]
  unfold psum
  rw [IsemWords.listSum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => by simp [wR]

theorem WA_eq : WA (stdWordR R D) = ((R.total : ℤ) - D).toNat := by
  have hL : (stdWordR R D).length = (stdInstR R).length + 2 := by
    simp [stdWordR, Lax434175.StandardReading.int]
  have h2 : (stdWordR R D).getD ((stdWordR R D).length - 2) 0 = if D < 0 then 1 else 0 := by
    rw [hL, Nat.add_sub_cancel, show (stdInstR R).length = (stdInstR R).length + 0 from rfl, stdWordR, getD_app]
    rfl
  have h1 : (stdWordR R D).getD ((stdWordR R D).length - 1) 0 = D.natAbs := by
    rw [hL, show (stdInstR R).length + 2 - 1 = (stdInstR R).length + 1 by omega, stdWordR, getD_app]
    rfl
  unfold WA
  rw [h1, h2, totA_eq]
  rcases lt_or_ge D 0 with hD | hD
  · rw [if_pos hD, if_neg (by norm_num)]; omega
  · rw [if_neg (not_lt.mpr hD), if_pos rfl]; omega

/-- The parsed word of an instance whose jobs all have a machine. -/
def mkX (W : ℕ) : List ℕ :=
  lay [R.jobs, R.machines, W] R.jobs (pR R) (dR R) (wR R) (mlN R)

theorem mlN_length_le {j : ℕ} : (mlN R j).length ≤ R.machines := by
  unfold mlN; split_ifs
  · exact (List.length_filter_le _ _).trans (by simp)
  · simp

theorem blk_le_length {k : ℕ} (hk : k < R.jobs) : (blkN R k).length ≤ (stdWordR R D).length := by
  have := psum_mono (fun k => (blkN R k).length) (show k + 1 ≤ R.jobs by omega)
  rw [psum_succ] at this
  rw [length_stdWordR]; omega

theorem mlR_length_le_length (j : Fin R.jobs) : (mlR R j).length ≤ (stdWordR R D).length := by
  have := blk_le_length R D j.isLt
  rw [blk_length] at this; omega

theorem cA_eq (j : Fin R.jobs) : cA (stdWordR R D) j = (mlR R j).length := by
  unfold cA; rw [cntA_eq]; have := mlR_length_le_length R D j; omega

theorem parse_good (hR : ∀ j, (R.elig j).Nonempty) :
    parseWord (stdWordR R D) = mkX R ((R.total : ℤ) - D).toNat := by
  have hm : ∀ k < R.jobs, 0 < R.machines := fun k hk => by
    obtain ⟨i, -⟩ := hR ⟨k, hk⟩; exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hbad : badA (stdWordR R D) = false := by
    unfold badA
    rw [nA_eq, List.any_eq_false]
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [cntA_eq R D ⟨k, hk'⟩]
    have : mlR R ⟨k, hk'⟩ ≠ [] := fun h => (mlR_nil_iff R _).mp h (hR _)
    simpa [List.length_eq_zero_iff] using this
  have hP : (List.range R.jobs).map (pA (stdWordR R D)) = (List.range R.jobs).map (pR R) :=
    List.map_congr_left fun k hk => by
      have hk' := List.mem_range.mp hk
      rw [pA_eq R D (hm k hk') ⟨k, hk'⟩]; simp [pR, hk']
  have hD : (List.range R.jobs).map (dA (stdWordR R D)) = (List.range R.jobs).map (dR R) :=
    List.map_congr_left fun k hk => by
      have hk' := List.mem_range.mp hk
      rw [dA_eq R D (by omega) ⟨k, hk'⟩]; simp [dR, hk']
  have hW : (List.range R.jobs).map (wA (stdWordR R D)) = (List.range R.jobs).map (wR R) :=
    List.map_congr_left fun k hk => by
      have hk' := List.mem_range.mp hk
      rw [wA_eq R D (by omega) ⟨k, hk'⟩]; simp [wR, hk']
  have hO : (List.range (R.jobs + 1)).map (offA (stdWordR R D)) =
      (List.range (R.jobs + 1)).map (psum fun j => (mlN R j).length) :=
    List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      unfold offA
      exact psum_congr fun k hk => by rw [cA_eq R D ⟨k, by omega⟩]; simp [mlN, show k < R.jobs by omega]
  have hT : ((List.range R.jobs).flatMap fun j => (List.range (cA (stdWordR R D) j)).map (mchA (stdWordR R D) j)) =
      (List.range R.jobs).flatMap (mlN R) :=
    List.flatMap_congr fun k hk => by
      have hk' := List.mem_range.mp hk
      rw [cA_eq R D ⟨k, hk'⟩]
      rw [List.map_congr_left fun t ht => mchA_eq R D ⟨k, hk'⟩ (List.mem_range.mp ht), map_range_getD]
      simp [mlN, hk']
  unfold parseWord
  rw [if_neg (by rw [hbad]; simp), nA_eq, mA_eq, WA_eq, hP, hD, hW, hO, hT]
  unfold mkX lay
  simp only [List.append_assoc]

theorem parse_bad (hR : ¬ ∀ j, (R.elig j).Nonempty) : parseWord (stdWordR R D) = [0, 0, 1] := by
  push Not at hR
  obtain ⟨j, hj⟩ := hR
  unfold parseWord
  rw [if_pos]
  unfold badA
  rw [nA_eq, List.any_eq_true]
  refine ⟨j, List.mem_range.mpr j.isLt, ?_⟩
  rw [cntA_eq, (mlR_nil_iff R j).mpr (by rw [Finset.not_nonempty_iff_eq_empty]; exact hj)]
  rfl

/-! ### Writing the scaled instance from the parsed word -/

variable (W : ℕ)

theorem mkX_length : (mkX R W).length = 3 + 4 * R.jobs + 1 + psum (fun j => (mlN R j).length) R.jobs :=
  lay_length _ _ _ _ _ _

theorem nB_mk : nB (mkX R W) = R.jobs := by
  unfold nB
  rw [show (mkX R W).getD 0 0 = R.jobs from lay_hd _ _ _ _ _ _ (k := 0) (by simp), mkX_length]; omega

theorem mB_mk : mB (mkX R W) = R.machines := lay_hd _ _ _ _ _ _ (k := 1) (by simp)
theorem WB_mk : WB (mkX R W) = W := lay_hd _ _ _ _ _ _ (k := 2) (by simp)

theorem pB_mk (j : Fin R.jobs) : pB (mkX R W) j = R.p j := by
  unfold pB; exact (lay_P [R.jobs, R.machines, W] R.jobs (pR R) (dR R) (wR R) (mlN R) j.isLt).trans (by simp [pR])

theorem dB_mk (j : Fin R.jobs) : dB (mkX R W) j = R.d j := by
  unfold dB; rw [nB_mk]
  exact (lay_D [R.jobs, R.machines, W] R.jobs (pR R) (dR R) (wR R) (mlN R) j.isLt).trans (by simp [dR])

theorem wB_mk (j : Fin R.jobs) : wB (mkX R W) j = R.w j := by
  unfold wB; rw [nB_mk]
  exact (lay_W [R.jobs, R.machines, W] R.jobs (pR R) (dR R) (wR R) (mlN R) j.isLt).trans (by simp [wR])

theorem oB_mk {i : ℕ} (hi : i ≤ R.jobs) : oB (mkX R W) i = psum (fun j => (mlN R j).length) i := by
  unfold oB; rw [nB_mk]; exact lay_O [R.jobs, R.machines, W] R.jobs _ _ _ _ hi

theorem mlN_eq (j : Fin R.jobs) : mlN R j = mlR R j := by simp [mlN]

theorem cB_mk (j : Fin R.jobs) : cB (mkX R W) j = (mlR R j).length := by
  unfold cB
  rw [oB_mk R W j.isLt, oB_mk R W j.isLt.le, psum_succ, mlN_eq, mkX_length]
  have := psum_mono (fun j => (mlN R j).length) (show j.val + 1 ≤ R.jobs from j.isLt)
  rw [psum_succ, mlN_eq] at this
  omega

theorem tB_mk (j : Fin R.jobs) {t : ℕ} (ht : t < (mlR R j).length) :
    tB (mkX R W) (oB (mkX R W) j + t) = (mlR R j).getD t 0 := by
  unfold tB
  rw [nB_mk, oB_mk R W j.isLt.le, show 4 + 4 * R.jobs + (psum (fun j => (mlN R j).length) j + t) =
    [R.jobs, R.machines, W].length + 4 * R.jobs + 1 + (psum (fun j => (mlN R j).length) j + t) by
      simp only [List.length_cons, List.length_nil]; omega]
  unfold mkX
  rw [lay_T, getD_flatMap_range _ j.isLt (by rw [mlN_eq]; exact ht), mlN_eq]

theorem sameB_mk (j k : Fin R.jobs) : sameB (mkX R W) j k = true ↔ R.Same j k := by
  unfold sameB Raw.Same
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  rw [pB_mk, dB_mk, dB_mk, cB_mk, cB_mk]
  have key : ((mlR R j).length = (mlR R k).length ∧ ∀ t < (mlR R j).length,
      tB (mkX R W) (oB (mkX R W) j + t) = tB (mkX R W) (oB (mkX R W) k + t)) ↔ R.elig k = R.elig j := by
    rw [← mlR_eq_iff]
    constructor
    · rintro ⟨hl, h⟩
      exact eq_of_getD hl.symm fun t ht => by
        rw [← tB_mk R W k ht, ← tB_mk R W j (by omega), h t (by omega)]
    · intro h
      refine ⟨by rw [h], fun t ht => ?_⟩
      rw [tB_mk R W j ht, tB_mk R W k (by rw [h]; exact ht), h]
  rw [← key]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem headB_mk (j : Fin R.jobs) : headB (mkX R W) j = true ↔ R.IsHead j := by
  unfold headB Raw.IsHead
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_false, List.mem_range]
  rw [pB_mk]
  refine and_congr Iff.rfl ⟨fun h k hk hs => ?_, fun h k hk => ?_⟩
  · have := h k hk
    rw [show k.val = (⟨k.val, k.isLt⟩ : Fin R.jobs) from rfl, (sameB_mk R W j _).mpr hs] at this
    exact absurd this (by simp)
  · have hs : ¬ R.Same j ⟨k, by omega⟩ := h ⟨k, by omega⟩ (Fin.mk_lt_mk.mpr (by exact hk))
    rw [← sameB_mk R W] at hs
    simpa using hs

theorem realB_mk (j : Fin R.jobs) : realB (mkX R W) j = true ↔ R.IsReal j := by
  unfold realB Raw.IsReal
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [pB_mk, dB_mk]

theorem r_eq (n m : ℕ) : min (2 ^ min m n) n = min n (2 ^ m) := by
  rcases le_or_gt m n with h | h
  · rw [min_eq_left h, min_comm]
  · rw [min_eq_right h.le]
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.le
    omega

theorem rB_mk : rB (mkX R W) = R.r := by
  unfold rB Raw.r; rw [mB_mk, nB_mk, r_eq]

theorem KB_mk : KB (mkX R W) = R.K := by unfold KB Raw.K; rw [rB_mk]

theorem slotB_mk (j : Fin R.jobs) : slotB (mkX R W) j = R.slot j := by
  classical
  unfold slotB Raw.slot
  rw [length_filter_range, Finset.card_filter]
  have e : ∀ k : Fin R.jobs, (if k < j ∧ R.IsHead k ∧ R.d k = R.d j then 1 else 0) =
      (fun k : ℕ => if k < j ∧ (headB (mkX R W) k && dB (mkX R W) k == dB (mkX R W) j) = true
        then 1 else 0) k := by
    intro k
    have hc : (k < j ∧ R.IsHead k ∧ R.d k = R.d j) ↔
        (k.val < j.val ∧ (headB (mkX R W) k && dB (mkX R W) k == dB (mkX R W) j) = true) := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      rw [headB_mk, dB_mk, dB_mk, Fin.lt_def]
    exact if_congr hc rfl rfl
  rw [Finset.sum_congr rfl fun k _ => e k, Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < j ∧
    (headB (mkX R W) k && dB (mkX R W) k == dB (mkX R W) j) = true then 1 else 0),
    ← IsemWords.listSum_range, ← psum]
  rw [psum_eq_of_zero _ j.isLt.le fun k hk1 _ => by rw [if_neg (by omega)]]
  exact psum_congr fun k hk => by simp [hk]

open Classical in
theorem hwB_mk (j : Fin R.jobs) :
    hwB (mkX R W) j = ∑ k ∈ Finset.univ.filter (R.Same j), R.w k := by
  classical
  unfold hwB
  rw [Finset.sum_filter, nB_mk]
  have e : ∀ k : Fin R.jobs, (if R.Same j k then R.w k else 0) =
      (fun k : ℕ => if sameB (mkX R W) j k then wB (mkX R W) k else 0) k := by
    intro k
    simp only
    rw [wB_mk]
    exact if_congr (sameB_mk R W j k).symm rfl rfl
  rw [Finset.sum_congr rfl fun k _ => e k, Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if sameB (mkX R W) j k then wB (mkX R W) k else 0), ← IsemWords.listSum_range]
  rfl

theorem keepB_mk (j : Fin R.jobs) : keepB (mkX R W) j = true ↔ R.IsReal j ∨ R.IsHead j := by
  unfold keepB; rw [Bool.or_eq_true, realB_mk, headB_mk]

theorem tgOut_mk (j : Fin R.jobs) :
    tgOut (mkX R W) j = if keepB (mkX R W) j then mlR R j else [R.machines] := by
  unfold tgOut
  split_ifs
  · rw [cB_mk, List.map_congr_left fun t ht => tB_mk R W j (List.mem_range.mp ht), map_range_getD]
  · rw [mB_mk]

theorem mOut_mk : mOut (mkX R W) = R.machines + 1 := by
  unfold mOut; rw [mkX_length, if_neg (by omega), mB_mk]

theorem build_eq : buildWord (mkX R W) = lay [R.jobs, R.machines + 1] R.jobs (pOut (mkX R W))
    (dOut (mkX R W)) (wOut (mkX R W)) (tgOut (mkX R W)) ++ [W] := by
  unfold buildWord lay
  rw [nB_mk, mOut_mk, WB_mk]
  simp only [List.append_assoc]
  rfl

open Classical in
/-- **The padded scaled instance is written.** -/
theorem build_mk (hR : ∀ j, (R.elig j).Nonempty) :
    EncodesDecisionInstance (buildWord (mkX R W)) (Lax434175.IsemLink.pad R.toIsem) W := by
  refine ⟨_, build_eq R W, encodes_lay (Lax434175.IsemLink.pad R.toIsem) _ _ _ _ (fun j => ?_)
    (fun j => ?_) (fun j => ?_) (fun j hj v hv => ?_) (fun j i => ?_)⟩
  · change Fin R.jobs at j
    show pOut (mkX R W) j = if R.IsReal j then R.K * R.p j - 2 * R.r - 2 else 1
    unfold pOut
    by_cases h : R.IsReal j
    · rw [if_pos ((realB_mk R W j).mpr h), if_pos h, KB_mk, rB_mk, pB_mk]
    · rw [if_neg (fun h' => h ((realB_mk R W j).mp h')), if_neg h]
  · change Fin R.jobs at j
    show dOut (mkX R W) j = if R.IsReal j then R.K * R.d j - R.r - 1
      else if R.IsHead j then R.K * R.d j + R.slot j + 1 else 1
    unfold dOut
    by_cases h : R.IsReal j
    · rw [if_pos ((realB_mk R W j).mpr h), if_pos h, KB_mk, rB_mk, dB_mk]
    · rw [if_neg (fun h' => h ((realB_mk R W j).mp h')), if_neg h]
      by_cases h' : R.IsHead j
      · rw [if_pos ((headB_mk R W j).mpr h'), if_pos h', KB_mk, dB_mk, slotB_mk]
      · rw [if_neg (fun h'' => h' ((headB_mk R W j).mp h'')), if_neg h']
  · change Fin R.jobs at j
    show wOut (mkX R W) j = if (R.toIsem.eligible j).Nonempty then R.toIsem.w j else 0
    unfold wOut
    by_cases h : R.IsReal j
    · rw [if_pos (show (R.toIsem.eligible j).Nonempty by rw [R.eligible_real h]; exact hR j)]
      show _ = if R.IsReal j then R.w j
        else if R.IsHead j then ∑ k ∈ Finset.univ.filter (R.Same j), R.w k else 0
      rw [if_pos ((realB_mk R W j).mpr h), if_pos h, wB_mk]
    · rw [if_neg (fun h' => h ((realB_mk R W j).mp h'))]
      by_cases h' : R.IsHead j
      · rw [if_pos (show (R.toIsem.eligible j).Nonempty by rw [R.eligible_head h']; exact hR j)]
        show _ = if R.IsReal j then R.w j
          else if R.IsHead j then ∑ k ∈ Finset.univ.filter (R.Same j), R.w k else 0
        rw [if_neg h, if_pos ((headB_mk R W j).mpr h'), if_pos h', hwB_mk]
      · rw [if_neg (show ¬ (R.toIsem.eligible j).Nonempty by rw [R.eligible_other h h']; simp),
          if_neg (fun h'' => h' ((headB_mk R W j).mp h''))]
  · rw [show j = (⟨j, hj⟩ : Fin R.jobs).val from rfl, tgOut_mk] at hv
    show v < R.machines + 1
    split_ifs at hv
    · exact Nat.lt_succ_of_lt (lt_of_mem_mlR R hv)
    · simp at hv; omega
  · change Fin R.jobs at j
    change Fin (R.machines + 1) at i
    show i ∈ (if (R.toIsem.eligible j).Nonempty then (R.toIsem.eligible j).map Fin.castSuccEmb
      else {Fin.last R.machines}) ↔ _
    rw [tgOut_mk]
    by_cases h : R.IsReal j ∨ R.IsHead j
    · have he : R.toIsem.eligible j = R.elig j := by
        rcases h with h | h
        · exact R.eligible_real h
        · exact R.eligible_head h
      rw [he, if_pos (hR j), if_pos ((keepB_mk R W j).mpr h), Finset.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (mem_mlR R j a).mpr ha
      · intro hi
        have hlt := lt_of_mem_mlR R hi
        exact ⟨⟨i.val, hlt⟩, (mem_mlR R j ⟨i.val, hlt⟩).mp hi, Fin.ext rfl⟩
    · have h1 : ¬ R.IsReal j := fun h' => h (Or.inl h')
      have h2 : ¬ R.IsHead j := fun h' => h (Or.inr h')
      rw [R.eligible_other h1 h2, if_neg (by simp), if_neg (fun h' => h ((keepB_mk R W j).mp h')),
        Finset.mem_singleton, List.mem_singleton, Fin.ext_iff, Fin.val_last]

end RawWord

open Lax759944.BinaryWordEncoding in
/-- **The word map writes the padded scaled instance**, when every job has a machine. -/
theorem toIsemWord_spec (R : Raw) (D : ℤ) (hR : ∀ j, (R.elig j).Nonempty) :
    EncodesDecisionInstance (toIsemWord (stdWordR R D)) (Lax434175.IsemLink.pad R.toIsem)
      ((R.total : ℤ) - D).toNat := by
  unfold toIsemWord; rw [parse_good R D hR]; exact build_mk R _ hR

/-- **Otherwise the word map writes a no-instance.** -/
theorem toIsemWord_no (R : Raw) (D : ℤ) (hR : ¬ ∀ j, (R.elig j).Nonempty) :
    toIsemWord (stdWordR R D) = [0, 0, 0, 1] := by
  unfold toIsemWord; rw [parse_bad R D hR, buildWord_bad]

end Lax434175Proofs.P200Programs
