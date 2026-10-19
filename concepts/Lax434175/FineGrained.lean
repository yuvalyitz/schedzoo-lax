import Lax434175.Results

/-!
---
title: Fine-grained hypotheses and reductions on short words
type: definition
---
The hypotheses of fine-grained complexity, stated in the style of the
exponential time hypothesis (`Results.ETH`): on the word RAM of lax-808846, with
short words, $\ell \ge c \log_2(|u| + M + 2)$ for the input $u$ with largest
number $M$, so that a program cannot pack many numbers into one word. Each is
about an explicit problem on words. Problems with numbers have them polynomial in
the input size, as the literature states these conjectures.

- **SETH**: for every $\varepsilon > 0$ there is $k$ such that no program decides
  the satisfiability of formulas with clauses of at most $k$ literals over $n$
  variables within $c\,2^{(1-\varepsilon)n}(|w|+1)^c$ instructions.
- **Orthogonal vectors**: given $n$ and $d$ and two lists of $n$ vectors in
  $\{0,1\}^d$, is some vector of the first list orthogonal to some of the
  second? For every $\varepsilon > 0$ there is $a$ such that with $d \le a \log_2 n$
  no program decides it within $c\,n^{2-\varepsilon}$.
- **3SUM**: given $n$ integers of absolute value at most $n^3$, do three of them
  (at different positions) sum to $0$? No program decides it within
  $c\,n^{2-\varepsilon}$, for any $\varepsilon > 0$.
- **APSP**: given a complete directed graph on $n$ vertices with integer arc
  lengths of absolute value at most $n^3$ and no negative cycle, write the
  matrix of shortest distances; no program does so within $c\,n^{3-\varepsilon}$.
- **Min-plus convolution**: given two lists of $n$ integers of absolute value
  at most $n^3$, write $c_k = \min_{i+j=k}(a_i + b_j)$; no program does so within
  $c\,n^{2-\varepsilon}$.
- **$k$-Clique**: with $\omega$ the infimum of the exponents $e$ such that a
  program multiplies $n \times n$ matrices of integers of absolute value at most
  $n$ within $c\,n^e$ instructions, for every $k \ge 3$ and $\varepsilon > 0$ no
  program decides whether a graph on $n$ vertices has $k$ pairwise adjacent
  vertices within $c\,n^{(\omega/3-\varepsilon)k}$.

Integers are written as sign and absolute value; vectors, lists and matrices
entry by entry after their sizes; a graph as $n$ and its adjacency matrix.

A **fine-grained reduction** from a problem on words to another is one program
that maps the words of the first to words of the second, keeps the answer, runs
within $c\,(T(u) + 1)$ instructions on short words, and writes no number above
$N(u)$, so that the word length on the target side is known.
-/

namespace Lax434175.FineGrained
open Lax434175.Results Lax808846.Ram
open Classical

open Classical in
/-- One program decides the words of `dom` against `L` within `c (T w + 1)`
instructions at every short word length. -/
def DecidesIn (dom : Set (List ℕ)) (L : List ℕ → Prop) (T : List ℕ → ℝ) (p : Program) (c : ℕ) :
    Prop :=
  ∀ w ∈ dom, ∀ ℓ, WordOk c w ℓ → ∃ t : ℕ, (t : ℝ) ≤ c * (T w + 1) ∧
    RunsTo ℓ p (w.length :: w) (if L w then [1] else [0]) t

/-- One program writes `F w` for the words of `dom` within `c (T w + 1)`
instructions at every short word length. -/
def ComputesIn (dom : Set (List ℕ)) (F : List ℕ → List ℕ) (T : List ℕ → ℝ) (p : Program) (c : ℕ) :
    Prop :=
  ∀ w ∈ dom, ∀ ℓ, WordOk c w ℓ → ∃ t : ℕ, (t : ℝ) ≤ c * (T w + 1) ∧ RunsTo ℓ p (w.length :: w) (F w) t

/-- An integer as sign and absolute value. -/
def int (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]

-- SETH

/-- The words of formulas on `n` variables with clauses of at most `k` literals. -/
def kCNF (k : ℕ) : Set (List ℕ) :=
  {w | ∃ n Φ, w = formulaWord n Φ ∧ ∀ C ∈ Φ, C.length ≤ k ∧ ∀ l ∈ C, l.index < n}

/-- The number of variables a formula word announces. -/
def vars (w : List ℕ) : ℕ := w.headD 0

/-- The strong exponential time hypothesis. -/
def SETH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ (p : Program) (c : ℕ),
    ¬ DecidesIn (kCNF k)
      (fun w => ∃ n Φ, w = formulaWord n Φ ∧ Lax429075.CNF.Satisfiable Φ)
      (fun w => (2 : ℝ) ^ ((1 - ε) * vars w) * (w.length + 1 : ℝ) ^ c) p c

-- Orthogonal vectors

/-- The word of an instance of orthogonal vectors. -/
def ovWord (n d : ℕ) (A B : Fin n → Fin d → Bool) : List ℕ :=
  [n, d] ++ (List.ofFn fun i => List.ofFn fun k => if A i k then 1 else 0).flatten ++
    (List.ofFn fun i => List.ofFn fun k => if B i k then 1 else 0).flatten

/-- The words of instances with `d ≤ a log₂ n`. -/
def OVWords (a : ℕ) : Set (List ℕ) :=
  {w | ∃ n d A B, w = ovWord n d A B ∧ d ≤ a * Nat.log 2 n}

/-- The orthogonal vectors hypothesis. -/
def OVH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, ∀ (p : Program) (c : ℕ),
    ¬ DecidesIn (OVWords a)
      (fun w => ∃ n d A B, w = ovWord n d A B ∧ ∃ i j, ∀ k, A i k = false ∨ B j k = false)
      (fun w => (w.headD 0 : ℝ) ^ (2 - ε)) p c

-- 3SUM

/-- The word of a list of integers. -/
def intsWord {n : ℕ} (a : Fin n → ℤ) : List ℕ := n :: (List.ofFn fun i => int (a i)).flatten

/-- The words of `n` integers of absolute value at most `n³`. -/
def SmallInts : Set (List ℕ) :=
  {w | ∃ (n : ℕ) (a : Fin n → ℤ), w = intsWord a ∧ ∀ i, (a i).natAbs ≤ n ^ 3}

/-- The 3SUM hypothesis. -/
def ThreeSumH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (p : Program) (c : ℕ),
    ¬ DecidesIn SmallInts
      (fun w => ∃ (n : ℕ) (a : Fin n → ℤ), w = intsWord a ∧
        ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ a i + a j + a k = 0)
      (fun w => (w.headD 0 : ℝ) ^ (2 - ε)) p c

-- APSP

/-- The word of a complete directed graph with arc lengths. -/
def graphWord {n : ℕ} (len : Fin n → Fin n → ℤ) : List ℕ :=
  n :: (List.ofFn fun i => (List.ofFn fun j => int (len i j)).flatten).flatten

/-- The length of a walk given by its list of vertices. -/
def walkLength {n : ℕ} (len : Fin n → Fin n → ℤ) : List (Fin n) → ℤ
  | a :: b :: rest => len a b + walkLength len (b :: rest)
  | _ => 0

/-- `δ` is the matrix of shortest distances: every walk from `i` to `j` is at
least `δ i j` long, and one has that length. -/
def Distances {n : ℕ} (len : Fin n → Fin n → ℤ) (δ : Fin n → Fin n → ℤ) : Prop :=
  ∀ i j, (∀ W : List (Fin n), W.head? = some i → W.getLast? = some j → δ i j ≤ walkLength len W) ∧
    ∃ W : List (Fin n), W.head? = some i ∧ W.getLast? = some j ∧ walkLength len W = δ i j

/-- No cycle has negative length. -/
def NoNegativeCycle {n : ℕ} (len : Fin n → Fin n → ℤ) : Prop :=
  ∀ W : List (Fin n), W.head? = W.getLast? → 0 ≤ walkLength len W

/-- The APSP hypothesis: no program writes the distance matrix within
`c n^{3-ε}`, for any function that writes it on the instances. -/
def APSPH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (p : Program) (c : ℕ) (F : List ℕ → List ℕ),
    (∀ n (len : Fin n → Fin n → ℤ), NoNegativeCycle len → (∀ i j, (len i j).natAbs ≤ n ^ 3) →
      ∃ δ, Distances len δ ∧ F (graphWord len) = (List.ofFn fun i => (List.ofFn fun j =>
        int (δ i j)).flatten).flatten) →
    ¬ ComputesIn {w | ∃ (n : ℕ) (len : Fin n → Fin n → ℤ), w = graphWord len ∧ NoNegativeCycle len ∧
        ∀ i j, (len i j).natAbs ≤ n ^ 3} F (fun w => (w.headD 0 : ℝ) ^ (3 - ε)) p c

-- Min-plus convolution

/-- The word of two lists of `n` integers. -/
def pairWord {n : ℕ} (a b : Fin n → ℤ) : List ℕ :=
  n :: (List.ofFn fun i => int (a i)).flatten ++ (List.ofFn fun i => int (b i)).flatten

/-- The min-plus convolution of two lists of `n ≥ 1` integers, entries `0` to `2n - 2`. -/
def minPlus {n : ℕ} (a b : Fin n → ℤ) (k : ℕ) : ℤ :=
  ((Finset.univ.filter fun p : Fin n × Fin n => p.1.val + p.2.val = k).image
    fun p => a p.1 + b p.2).min.getD 0

/-- The min-plus convolution hypothesis. -/
def MinPlusH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (p : Program) (c : ℕ),
    ¬ ComputesIn {w | ∃ (n : ℕ) (a b : Fin n → ℤ), w = pairWord a b ∧
        ∀ i, (a i).natAbs ≤ n ^ 3 ∧ (b i).natAbs ≤ n ^ 3}
      (fun w => (List.ofFn fun k : Fin (2 * w.headD 0 - 1) => int (if h : ∃ (n : ℕ) (a b : Fin n → ℤ),
          w = pairWord a b then minPlus h.choose_spec.choose h.choose_spec.choose_spec.choose k
          else 0)).flatten)
      (fun w => (w.headD 0 : ℝ) ^ (2 - ε)) p c

-- k-Clique

/-- The word of a square matrix of integers. -/
def matrixWord {n : ℕ} (A : Fin n → Fin n → ℤ) : List ℕ :=
  n :: (List.ofFn fun i => (List.ofFn fun j => int (A i j)).flatten).flatten

/-- The exponents `e` of matrix multiplication: one program writes the product
of two `n × n` matrices with entries of absolute value at most `n` within
`c n^e` instructions. -/
def MultipliesIn (e : ℝ) : Prop :=
  ∃ (p : Program) (c : ℕ), ComputesIn
    {w | ∃ (n : ℕ) (A B : Fin n → Fin n → ℤ), w = matrixWord A ++ (matrixWord B).tail ∧
      ∀ i j, (A i j).natAbs ≤ n ∧ (B i j).natAbs ≤ n}
    (fun w => if h : ∃ (n : ℕ) (A B : Fin n → Fin n → ℤ), w = matrixWord A ++ (matrixWord B).tail then
      matrixWord fun i j => ∑ k, h.choose_spec.choose i k * h.choose_spec.choose_spec.choose k j
      else [])
    (fun w => (w.headD 0 : ℝ) ^ e) p c

/-- The exponent `ω` of matrix multiplication on the word RAM. -/
noncomputable def omega : ℝ := sInf {e | MultipliesIn e}

/-- The word of a graph: `n` and its adjacency matrix. -/
def adjWord {n : ℕ} (G : Fin n → Fin n → Bool) : List ℕ :=
  n :: (List.ofFn fun i => List.ofFn fun j => if G i j then 1 else 0).flatten

/-- The `k`-clique hypothesis. -/
def KCliqueH : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ (p : Program) (c : ℕ),
    ¬ DecidesIn {w | ∃ (n : ℕ) (G : Fin n → Fin n → Bool), w = adjWord G ∧ ∀ i j, G i j = G j i}
      (fun w => ∃ (n : ℕ) (G : Fin n → Fin n → Bool), w = adjWord G ∧
        ∃ S : Finset (Fin n), S.card = k ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → G i j = true)
      (fun w => (w.headD 0 : ℝ) ^ ((omega / 3 - ε) * k)) p c

-- Reductions

/-- A fine-grained reduction: one program maps the words of `dom` to words of
`dom'`, keeps the answer, runs within `c (T u + 1)` instructions on short words,
and writes no number above `N u`. -/
def FineReduces (dom dom' : Set (List ℕ)) (L L' : List ℕ → Prop) (T : List ℕ → ℝ)
    (N : List ℕ → ℕ) : Prop :=
  ∃ (f : List ℕ → List ℕ) (p : Program) (c : ℕ), ComputesIn dom f T p c ∧
    ∀ u ∈ dom, f u ∈ dom' ∧ (L u ↔ L' (f u)) ∧ maxEntry (f u) ≤ N u

end Lax434175.FineGrained
