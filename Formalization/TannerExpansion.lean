import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card

import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Formalization.ExpanderMixing
import Formalization.DiscreteCheeger

open scoped BigOperators Matrix Finset
open Classical


/-!
# Tanner's Vertex Expansion Bound for Regular Graphs

This module formalizes **Tanner's Vertex Expansion Bound** (R. Michael Tanner, 1984),
a fundamental theorem in spectral graph theory and coding theory establishing a quantitative
lower bound on the vertex expansion (neighborhood size $|N(S)|$) of subsets in a $d$-regular graph
in terms of the spectral expansion parameter $\lambda = \lambda(G) = \max_{i \ge 2} |\lambda_i|$.

## Mathematical Overview

Let $G = (V, E)$ be a $d$-regular graph on $n = |V|$ vertices.
For any subset $S \subseteq V$, its open neighborhood is:
$$N(S) = \{ v \in V \mid \exists u \in S, \{u, v\} \in E \}$$

### 1. Tanner's Vertex Expansion Theorem
For any non-empty subset $S \subseteq V$ ($0 < |S|$):
$$|N(S)| \ge \frac{d^2 |S|}{\frac{d^2 - \lambda^2}{n} |S| + \lambda^2}$$

Equivalently, the vertex expansion ratio satisfies:
$$\frac{|N(S)|}{|S|} \ge \frac{d^2}{(d^2 - \lambda^2) \frac{|S|}{n} + \lambda^2}$$

### 2. Key Corollaries & Limiting Regimes

1. **Small-Set Expansion**: If $|S| \le \alpha n$, then:
   $$|N(S)| \ge \frac{d^2}{\alpha (d^2 - \lambda^2) + \lambda^2} |S|$$
   In the extreme limit $\alpha \to 0$ (very small sets), the expansion factor approaches $d^2 / \lambda^2$.

2. **Ramanujan Graphs**: For graphs satisfying the optimal Ramanujan bound $\lambda \le 2\sqrt{d-1}$:
   $$|N(S)| \ge \frac{d^2 |S|}{\frac{(d-2)^2}{n} |S| + 4(d-1)}$$
   For small sets in Ramanujan graphs, $|N(S)| \ge \frac{d^2}{4(d-1)} |S| \approx \frac{d}{4} |S|$.

3. **Subsets of Size $\le n/2$**: For any non-empty $S$ with $|S| \le n/2$:
   $$|N(S)| \ge \frac{2 d^2}{d^2 + \lambda^2} |S|$$
   and the expansion margin satisfies:
   $$|N(S)| - |S| \ge \frac{d^2 - \lambda^2}{d^2 + \lambda^2} |S|$$

## Proof Strategy

The formal proof proceeds in 5 stages:
- **Part 1**: Adjacency operator $A f(u) = \sum_v A_{uv} f(v)$, neighborhood $N(S)$, $\sum_{u \in N(S)} A \mathbf{1}_S(u) = d|S|$.
- **Part 2**: Cauchy-Schwarz inequality over $N(S)$: $(d |S|)^2 \le |N(S)| \cdot \|A \mathbf{1}_S\|^2$.
- **Part 3**: Orthogonal spectral decomposition $\mathbf{1}_S = \mathbf{1}_S^\parallel + \mathbf{1}_S^\perp$ and Pythagorean identity.
- **Part 4**: Variational operator norm bound $\|A \mathbf{1}_S^\perp\|^2 \le \lambda^2 \|\mathbf{1}_S^\perp\|^2 = \lambda^2 |S|(1 - |S|/n)$,
  yielding $\|A \mathbf{1}_S\|^2 \le |S| (\frac{d^2 - \lambda^2}{n}|S| + \lambda^2)$.
- **Part 5**: Tanner's theorem by combining Cauchy-Schwarz and spectral bounds, canceling $|S|$, and deriving corollaries.

## References

- Tanner, R. M. (1984). *Explicit construction of concentrators from generalized $N$-gons*.
  SIAM Journal on Algebraic and Discrete Methods, 5(3), 287–293.
- Alon, N., & Spencer, J. (2016). *The Probabilistic Method* (4th ed.). Wiley.
- Hoory, S., Linial, N., & Wigderson, A. (2006). *Expander graphs and their applications*.
  Bulletin of the American Mathematical Society, 43(4), 439–561.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TannerExpansion

open ExpanderMixing


/-! ### Part 1: Graph Adjacency Operator & Neighborhood -/

/-- The graph adjacency operator $A : \mathbb{R}^V \to \mathbb{R}^V$ acting on vertex functions. -/
def adjOp (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : V → ℝ :=
  fun u => ∑ v : V, adjacencyMatrix G u v * f v

/-- The open neighborhood of a vertex set $S \subseteq V$: $N(S) = \bigcup_{u \in S} N(u)$. -/
def neighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.biUnion S (fun u => G.neighborFinset u)

/-- A vertex $v$ belongs to $N(S)$ iff there is some $u \in S$ adjacent to $v$. -/
theorem mem_neighborhood_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    v ∈ neighborhood G S ↔ ∃ u ∈ S, G.Adj u v := by
  simp [neighborhood, SimpleGraph.mem_neighborFinset]

/-- The adjacency operator applied to the indicator $\mathbf{1}_S$ evaluates to the sum
of adjacency entries over $S$. -/
theorem adjOp_indicator_apply (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u : V) :
    adjOp G (indicator S) u = ∑ v ∈ S, adjacencyMatrix G u v :=
  sum_mul_indicator S (fun v => adjacencyMatrix G u v)

/-- If $u \notin N(S)$, then $(A \mathbf{1}_S)(u) = 0$. -/
theorem adjOp_indicator_zero_of_not_mem_neighborhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u : V) (hu : u ∉ neighborhood G S) :
    adjOp G (indicator S) u = 0 := by
  rw [adjOp_indicator_apply, Finset.sum_eq_zero]
  intro v hv
  dsimp [adjacencyMatrix]
  exact ite_eq_right_iff.2 fun h => (hu ((mem_neighborhood_iff G S u).2 ⟨v, hv, h.symm⟩)).elim

/-- Total sum of $(A \mathbf{1}_S)(u)$ over all $u \in V$ is $d |S|$. -/
theorem sum_adjOp_indicator_eq (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) :
    (∑ u : V, adjOp G (indicator S) u) = (d : ℝ) * (S.card : ℝ) := by
  dsimp [adjOp]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_adj_col_eq_degree G hreg, ← Finset.mul_sum, sum_indicator_univ]

/-- Total sum of $(A \mathbf{1}_S)(u)$ restricted to the neighborhood $N(S)$ is $d |S|$. -/
theorem sum_neighborhood_adjOp_indicator_eq (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) :
    (∑ u ∈ neighborhood G S, adjOp G (indicator S) u) = (d : ℝ) * (S.card : ℝ) := by
  rw [← sum_adjOp_indicator_eq G hreg S, ← Finset.sum_subset (Finset.subset_univ _)]
  exact fun u _ hu => adjOp_indicator_zero_of_not_mem_neighborhood G S u hu

/-! ### Part 2: Cauchy-Schwarz on the Neighborhood -/

omit [Fintype V] [DecidableEq V] in
/-- Cauchy-Schwarz inequality for sums of real functions over a finite set:
$(\sum_{x \in s} f(x))^2 \le |s| \sum_{x \in s} f(x)^2$. -/
theorem cauchy_schwarz_finset (s : Finset V) (f : V → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * (∑ x ∈ s, (f x) ^ 2) := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f

/-- The squared $\ell^2$-norm of $(A \mathbf{1}_S)$ equals the sum of squares over the neighborhood $N(S)$. -/
theorem normSq_adjOp_indicator_eq_sum_neighborhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    normSq (adjOp G (indicator S)) = ∑ u ∈ neighborhood G S, (adjOp G (indicator S) u) ^ 2 := by
  simp only [normSq, innerProduct, sq]
  rw [← Finset.sum_subset (Finset.subset_univ _)]
  intro u _ hu
  simp [adjOp_indicator_zero_of_not_mem_neighborhood G S u hu]

/--
**Cauchy-Schwarz Inequality for $A \mathbf{1}_S$ on $N(S)$**:
$$(d |S|)^2 \le |N(S)| \cdot \|A \mathbf{1}_S\|^2$$
-/
theorem cauchy_schwarz_neighborhood (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) :
    ((d : ℝ) * (S.card : ℝ)) ^ 2 ≤ ((neighborhood G S).card : ℝ) * normSq (adjOp G (indicator S)) := by
  have := cauchy_schwarz_finset (neighborhood G S) (adjOp G (indicator S))
  rwa [sum_neighborhood_adjOp_indicator_eq G hreg, ← normSq_adjOp_indicator_eq_sum_neighborhood] at this

/-! ### Part 3: Spectral Decomposition of $A \mathbf{1}_S$ -/

/-- Decomposition of the indicator vector $\mathbf{1}_S = \mathbf{1}_S^\parallel + \mathbf{1}_S^\perp$. -/
theorem indicator_eq_decompParallel_add_decompPerp (S : Finset V) (u : V) :
    indicator S u = decompParallel S u + decompPerp S u := by
  dsimp [decompParallel, decompPerp]; ring

/-- Linearity of the adjacency operator across the orthogonal decomposition:
$A \mathbf{1}_S = A \mathbf{1}_S^\parallel + A \mathbf{1}_S^\perp$. -/
theorem adjOp_indicator_eq_add (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u : V) :
    adjOp G (indicator S) u = adjOp G (decompParallel S) u + adjOp G (decompPerp S) u := by
  simp_rw [adjOp, indicator_eq_decompParallel_add_decompPerp S, mul_add, Finset.sum_add_distrib]

omit [DecidableEq V] in
/-- The parallel component maps to the constant vector $\frac{d |S|}{n} \mathbf{1}$. -/
theorem adjOp_decompParallel (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) (u : V) :
    adjOp G (decompParallel S) u = (d : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by
  dsimp [adjOp, decompParallel]
  simp_rw [mul_div_right_comm, ← Finset.sum_mul, sum_adj_row_eq_degree G hreg]
  ring

/-- The perpendicular component after applying $A$ is orthogonal to the all-ones vector:
$A \mathbf{1}_S^\perp \in \mathbf{1}^\perp$. -/
theorem adjOp_decompPerp_orthogonal (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) (hn : Fintype.card V ≠ 0) :
    isOrthogonalToOnes (adjOp G (decompPerp S)) := by
  dsimp [isOrthogonalToOnes, adjOp]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_adj_col_eq_degree G hreg, ← Finset.mul_sum]
  rw [decompPerp_orthogonal S hn, mul_zero]

omit [DecidableEq V] in
/-- The squared norm of the parallel component:
$\|A \mathbf{1}_S^\parallel\|^2 = \frac{d^2 |S|^2}{n}$. -/
theorem normSq_adjOp_decompParallel (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S : Finset V) :
    normSq (adjOp G (decompParallel S)) = (d : ℝ) ^ 2 * (S.card : ℝ) ^ 2 / (Fintype.card V : ℝ) := by
  have h_app : ∀ u : V, adjOp G (decompParallel S) u = (d : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) :=
    adjOp_decompParallel G hreg S
  simp only [normSq, innerProduct, h_app, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnc]

/-- Pythagorean theorem for the spectral decomposition:
$\|A \mathbf{1}_S\|^2 = \|A \mathbf{1}_S^\parallel\|^2 + \|A \mathbf{1}_S^\perp\|^2$. -/
theorem normSq_adjOp_indicator_decomp (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S : Finset V) :
    normSq (adjOp G (indicator S)) =
      normSq (adjOp G (decompParallel S)) + normSq (adjOp G (decompPerp S)) := by
  have h_cross : (∑ u : V, 2 * (adjOp G (decompParallel S) u) * (adjOp G (decompPerp S) u)) = 0 := by
    simp_rw [adjOp_decompParallel G hreg, ← Finset.mul_sum]
    rw [adjOp_decompPerp_orthogonal G hreg S hn, mul_zero]
  simp only [normSq, innerProduct, adjOp_indicator_eq_add G S]
  have h_alg : ∀ u : V, (adjOp G (decompParallel S) u + adjOp G (decompPerp S) u) * (adjOp G (decompParallel S) u + adjOp G (decompPerp S) u) =
      (adjOp G (decompParallel S) u) * (adjOp G (decompParallel S) u) +
      (adjOp G (decompPerp S) u) * (adjOp G (decompPerp S) u) +
      2 * (adjOp G (decompParallel S) u) * (adjOp G (decompPerp S) u) := by
    intro u; ring
  simp_rw [h_alg, Finset.sum_add_distrib, h_cross, add_zero]

/-! ### Part 4: Spectral Bound on the Orthogonal Component -/


omit [DecidableEq V] in
/-- Bilinear Cauchy-Schwarz bound for the adjacency operator:
$\langle u, A v \rangle^2 \le d^2 \|u\|^2 \|v\|^2$. -/
theorem innerProduct_adjOp_sq_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (u v : V → ℝ) :
    (innerProduct u (adjOp G v)) ^ 2 ≤ (d : ℝ) ^ 2 * normSq u * normSq v := by
  dsimp [innerProduct, adjOp, normSq]
  have h_inner_sq : ∀ x y : V, (adjacencyMatrix G x y * u x) * (adjacencyMatrix G x y * v y) =
      u x * (adjacencyMatrix G x y * v y) := by
    intro x y; dsimp [adjacencyMatrix]; split_ifs <;> ring
  have h_lhs : (∑ x : V, u x * ∑ y : V, adjacencyMatrix G x y * v y) =
      ∑ p : V × V, (adjacencyMatrix G p.1 p.2 * u p.1) * (adjacencyMatrix G p.1 p.2 * v p.2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum, ← h_inner_sq]
  rw [h_lhs]
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : V × V => adjacencyMatrix G p.1 p.2 * u p.1)
    (fun p : V × V => adjacencyMatrix G p.1 p.2 * v p.2)
  have h_mat_sq : ∀ (a : ℝ) (x y : V), (adjacencyMatrix G x y * a) ^ 2 = adjacencyMatrix G x y * a ^ 2 :=
    fun a x y => by dsimp [adjacencyMatrix]; split_ifs <;> ring
  have h_left : (∑ p : V × V, (adjacencyMatrix G p.1 p.2 * u p.1) ^ 2) = (d : ℝ) * ∑ x : V, (u x) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [h_mat_sq, ← Finset.sum_mul, sum_adj_row_eq_degree G hreg, ← Finset.mul_sum]
  have h_right : (∑ p : V × V, (adjacencyMatrix G p.1 p.2 * v p.2) ^ 2) = (d : ℝ) * ∑ y : V, (v y) ^ 2 := by
    rw [Fintype.sum_prod_type_right]
    simp_rw [h_mat_sq, ← Finset.sum_mul, sum_adj_col_eq_degree G hreg, ← Finset.mul_sum]
  have h_sq_sum_u : (∑ x : V, u x * u x) = ∑ x : V, (u x) ^ 2 := by simp_rw [sq]
  have h_sq_sum_v : (∑ x : V, v x * v x) = ∑ x : V, (v x) ^ 2 := by simp_rw [sq]
  rw [h_left, h_right] at h_cs
  rw [h_sq_sum_u, h_sq_sum_v]
  have : ((d : ℝ) * ∑ x : V, (u x) ^ 2) * ((d : ℝ) * ∑ y : V, (v y) ^ 2) =
      (d : ℝ) ^ 2 * (∑ x : V, (u x) ^ 2) * (∑ y : V, (v y) ^ 2) := by ring
  rwa [this] at h_cs

omit [DecidableEq V] in
/-- Squared norm is the sum of component squares. -/
theorem normSq_eq_sum_sq (v : V → ℝ) : normSq v = ∑ u : V, (v u) ^ 2 := by
  simp only [normSq, innerProduct, sq]

omit [DecidableEq V] in
/-- Squared norm is non-negative. -/
theorem normSq_nonneg (v : V → ℝ) : 0 ≤ normSq v := by
  rw [normSq_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq V] in
/-- Squared norm is zero if and only if the vector is zero. -/
theorem normSq_eq_zero_iff (v : V → ℝ) : normSq v = 0 ↔ v = 0 := by
  simp [normSq_eq_sum_sq, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _), funext_iff]

omit [DecidableEq V] in
/-- Squared norm is strictly positive for any non-zero vector. -/
theorem normSq_pos_of_ne_zero {v : V → ℝ} (hne : v ≠ 0) : 0 < normSq v :=
  lt_of_le_of_ne (normSq_nonneg v) (Ne.symm (mt (normSq_eq_zero_iff v).mp hne))

omit [DecidableEq V] in
/-- If $w$ is orthogonal to $\mathbf{1}$, then $A w$ is also orthogonal to $\mathbf{1}$. -/
theorem isOrthogonalToOnes_adjOp (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (w : V → ℝ) (hw : isOrthogonalToOnes w) :
    isOrthogonalToOnes (adjOp G w) := by
  dsimp [isOrthogonalToOnes, adjOp]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_adj_col_eq_degree G hreg, ← Finset.mul_sum]
  dsimp [isOrthogonalToOnes] at hw
  rw [hw, mul_zero]

omit [DecidableEq V] in
/-- The set in the definition of $\lambda(G)$ is bounded above by $d$. -/
theorem bddAbove_spectralExpansionParameter_set (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) :
    BddAbove { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) } := by
  use (d : ℝ)
  rintro x ⟨u, v, hu, hv, _, _, rfl⟩
  have hu_pos : 0 < normSq u := normSq_pos_of_ne_zero hu
  have hv_pos : 0 < normSq v := normSq_pos_of_ne_zero hv
  have h_denom_pos : 0 < Real.sqrt (normSq u) * Real.sqrt (normSq v) :=
    mul_pos (Real.sqrt_pos.mpr hu_pos) (Real.sqrt_pos.mpr hv_pos)
  have h_sq := innerProduct_adjOp_sq_le G hreg u v
  rw [← sq_abs (innerProduct u (adjOp G v))] at h_sq
  have h_rhs : (d : ℝ) ^ 2 * normSq u * normSq v = ((d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hu_pos.le, Real.sq_sqrt hv_pos.le]; ring
  rw [h_rhs] at h_sq
  have h_nonneg : 0 ≤ (d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by positivity
  have h_le : |innerProduct u (adjOp G v)| ≤ (d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by
    have := sq_le_sq.mp h_sq
    rwa [abs_abs, abs_of_nonneg h_nonneg] at this
  exact (div_le_iff₀ h_denom_pos).mpr h_le

omit [DecidableEq V] in
/-- Operator norm spectral bound on the orthogonal complement $\mathbf{1}^\perp$:
$\|A w\|^2 \le \lambda(G)^2 \|w\|^2$ for any $w \in \mathbf{1}^\perp$. -/
theorem spectral_operator_norm_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (w : V → ℝ) (hw : isOrthogonalToOnes w) :
    normSq (adjOp G w) ≤ (spectralExpansionParameter G) ^ 2 * normSq w := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [normSq, innerProduct, adjOp]
  rcases eq_or_ne (adjOp G w) 0 with hu0 | hu0
  · simp [hu0, normSq, innerProduct]
    exact mul_nonneg (sq_nonneg _) (normSq_nonneg w)
  · let u := adjOp G w
    have hu_orth : isOrthogonalToOnes u := isOrthogonalToOnes_adjOp G hreg w hw
    have hu_pos : 0 < normSq u := normSq_pos_of_ne_zero hu0
    have hw_pos : 0 < normSq w := normSq_pos_of_ne_zero hw0
    have h_elem : |normSq u| / (Real.sqrt (normSq u) * Real.sqrt (normSq w)) ∈
        { |innerProduct u' (fun x => ∑ y : V, adjacencyMatrix G x y * v' y)| /
          (Real.sqrt (normSq u') * Real.sqrt (normSq v')) |
          (u' : V → ℝ) (v' : V → ℝ) (_ : u' ≠ 0) (_ : v' ≠ 0)
          (_ : isOrthogonalToOnes u') (_ : isOrthogonalToOnes v') } :=
      ⟨u, w, hu0, hw0, hu_orth, hw, rfl⟩
    have h_le_sup := le_csSup (bddAbove_spectralExpansionParameter_set G hreg) h_elem
    rw [abs_of_pos hu_pos] at h_le_sup
    have h_sim : normSq u / (Real.sqrt (normSq u) * Real.sqrt (normSq w)) = Real.sqrt (normSq u) / Real.sqrt (normSq w) := by
      have h_ne : Real.sqrt (normSq u) ≠ 0 := Real.sqrt_ne_zero'.mpr hu_pos
      have h_split : normSq u = Real.sqrt (normSq u) * Real.sqrt (normSq u) := by
        rw [← Real.sqrt_mul hu_pos.le, Real.sqrt_mul_self hu_pos.le]
      have h_frac : normSq u / (Real.sqrt (normSq u) * Real.sqrt (normSq w)) =
          (Real.sqrt (normSq u) * Real.sqrt (normSq u)) / (Real.sqrt (normSq u) * Real.sqrt (normSq w)) := by
        rw [← h_split]
      rw [h_frac, mul_div_mul_left _ _ h_ne]
    rw [h_sim] at h_le_sup
    have h_sqrt_w_pos : 0 < Real.sqrt (normSq w) := Real.sqrt_pos.mpr hw_pos
    have h_mul_le : Real.sqrt (normSq u) ≤ spectralExpansionParameter G * Real.sqrt (normSq w) :=
      (div_le_iff₀ h_sqrt_w_pos).mp h_le_sup
    have h_sq : (Real.sqrt (normSq u)) ^ 2 ≤ (spectralExpansionParameter G * Real.sqrt (normSq w)) ^ 2 := by
      have : 0 ≤ Real.sqrt (normSq u) := Real.sqrt_nonneg _
      have : 0 ≤ spectralExpansionParameter G * Real.sqrt (normSq w) :=
        mul_nonneg (spectralExpansionParameter_nonneg G) (Real.sqrt_nonneg _)
      nlinarith [h_mul_le]
    rw [Real.sq_sqrt hu_pos.le, mul_pow, Real.sq_sqrt hw_pos.le] at h_sq
    exact h_sq

/-- Bounding the norm of $A \mathbf{1}_S^\perp$ by $\lambda^2 |S|(1 - |S|/n)$. -/
theorem normSq_adjOp_decompPerp_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S : Finset V) :
    normSq (adjOp G (decompPerp S)) ≤
      (spectralExpansionParameter G) ^ 2 * (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
  have := spectral_operator_norm_bound G hreg (decompPerp S) (decompPerp_orthogonal S hn)
  rw [decompPerp_normSq S hn] at this
  have h_ring : (spectralExpansionParameter G) ^ 2 * ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) =
      (spectralExpansionParameter G) ^ 2 * (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by ring
  rwa [← h_ring]

/--
**Upper Bound on $\|A \mathbf{1}_S\|^2$ via Spectral Decomposition**:
$$\|A \mathbf{1}_S\|^2 \le |S| \left( \frac{d^2 - \lambda^2}{n} |S| + \lambda^2 \right)$$
-/
theorem normSq_adjOp_indicator_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S : Finset V) :
    normSq (adjOp G (indicator S)) ≤
      (S.card : ℝ) * (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2) := by
  rw [normSq_adjOp_indicator_decomp G hreg hn S, normSq_adjOp_decompParallel G hreg hn S]
  have h_perp := normSq_adjOp_decompPerp_le G hreg hn S
  have h_alg : (d : ℝ) ^ 2 * (S.card : ℝ) ^ 2 / (Fintype.card V : ℝ) +
      (spectralExpansionParameter G) ^ 2 * (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) =
      (S.card : ℝ) * (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2) := by ring
  linarith

/-! ### Part 5: Tanner's Vertex Expansion Theorem and Corollaries -/

omit [DecidableEq V] in
/-- Upper bound $\lambda(G) \le d$ for any $d$-regular graph $G$. -/
theorem spectralExpansionParameter_le_d (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) :
    spectralExpansionParameter G ≤ (d : ℝ) := by
  dsimp [spectralExpansionParameter]
  by_cases h_empty : { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }.Nonempty
  · apply csSup_le h_empty
    rintro x ⟨u, v, hu, hv, _, _, rfl⟩
    have hu_pos : 0 < normSq u := normSq_pos_of_ne_zero hu
    have hv_pos : 0 < normSq v := normSq_pos_of_ne_zero hv
    have h_denom_pos : 0 < Real.sqrt (normSq u) * Real.sqrt (normSq v) :=
      mul_pos (Real.sqrt_pos.mpr hu_pos) (Real.sqrt_pos.mpr hv_pos)
    have h_sq := innerProduct_adjOp_sq_le G hreg u v
    rw [← sq_abs (innerProduct u (adjOp G v))] at h_sq
    have h_rhs : (d : ℝ) ^ 2 * normSq u * normSq v = ((d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hu_pos.le, Real.sq_sqrt hv_pos.le]; ring
    rw [h_rhs] at h_sq
    have h_nonneg : 0 ≤ (d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by positivity
    have h_le : |innerProduct u (adjOp G v)| ≤ (d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by
      have := sq_le_sq.mp h_sq
      rwa [abs_abs, abs_of_nonneg h_nonneg] at this
    exact (div_le_iff₀ h_denom_pos).mpr h_le
  · rw [Set.not_nonempty_iff_eq_empty.mp h_empty, Real.sSup_empty]
    positivity

omit [DecidableEq V] in
/-- $\lambda(G)^2 \le d^2$ for any $d$-regular graph $G$. -/
theorem sq_spectralExpansionParameter_le_sq_d (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) :
    (spectralExpansionParameter G) ^ 2 ≤ (d : ℝ) ^ 2 := by
  have := spectralExpansionParameter_le_d G hreg
  have := spectralExpansionParameter_nonneg G
  nlinarith

omit [DecidableEq V] in
/-- Positivity of the Tanner denominator for non-empty $S \subseteq V$ and $d > 0$. -/
theorem tanner_denominator_pos (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hn : Fintype.card V ≠ 0) (hd : 0 < d) (S : Finset V) (hS : 0 < S.card) :
    0 < ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) +
        (spectralExpansionParameter G) ^ 2 := by
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  have hs_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ S)
  have h_eq : ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) +
        (spectralExpansionParameter G) ^ 2 =
      (d : ℝ) ^ 2 * (S.card : ℝ) / (Fintype.card V : ℝ) +
        (spectralExpansionParameter G) ^ 2 * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by ring
  rw [h_eq]
  have h1 : 0 < (d : ℝ) ^ 2 * (S.card : ℝ) / (Fintype.card V : ℝ) := by
    have : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  have h2 : 0 ≤ (spectralExpansionParameter G) ^ 2 * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
    have : 0 ≤ 1 - (S.card : ℝ) / (Fintype.card V : ℝ) := by
      rw [sub_nonneg]; exact (div_le_one hn_pos).mpr hs_le
    positivity
  linarith

/--
**Tanner's Vertex Expansion Theorem** (R. M. Tanner, 1984):
For any $d$-regular graph $G$ on $n$ vertices ($n \ne 0$, $d > 0$) and any non-empty subset $S \subseteq V$,
the size of the open neighborhood $N(S)$ satisfies:
$$|N(S)| \ge \frac{d^2 |S|}{\frac{d^2 - \lambda^2}{n} |S| + \lambda^2}$$
where $\lambda = \lambda(G) = \text{spectralExpansionParameter } G$.
-/
theorem tanner_vertex_expansion_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S : Finset V) (hS : 0 < S.card) :
    ((d : ℝ) ^ 2 * (S.card : ℝ)) /
      (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2) ≤
    ((neighborhood G S).card : ℝ) := by
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  have h_cs := cauchy_schwarz_neighborhood G hreg S
  have h_spec := normSq_adjOp_indicator_le G hreg hn S
  have h_denom_pos := tanner_denominator_pos G hn hd S hS
  have h_neigh_nonneg : 0 ≤ ((neighborhood G S).card : ℝ) := Nat.cast_nonneg _
  have h_comb := le_trans h_cs (mul_le_mul_of_nonneg_left h_spec h_neigh_nonneg)
  rw [div_le_iff₀ h_denom_pos]
  nlinarith

/--
**Tanner's Expansion Ratio Bound**:
For any non-empty subset $S \subseteq V$, the vertex expansion ratio $|N(S)| / |S|$ satisfies:
$$\frac{|N(S)|}{|S|} \ge \frac{d^2}{(d^2 - \lambda^2)\frac{|S|}{n} + \lambda^2}$$
-/
theorem tanner_expansion_ratio_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S : Finset V) (hS : 0 < S.card) :
    ((d : ℝ) ^ 2) /
      (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2) ≤
    ((neighborhood G S).card : ℝ) / (S.card : ℝ) := by
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  have h_bound := tanner_vertex_expansion_bound G hreg hn hd S hS
  have h_eq : (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2) =
      (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2) := by ring
  rw [h_eq] at h_bound
  rw [le_div_iff₀ hs_pos]
  have h_cancel : ((d : ℝ) ^ 2 * (S.card : ℝ)) / (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2) =
      ((d : ℝ) ^ 2 / (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) := by ring
  rwa [h_cancel] at h_bound

/--
**Small Set Expansion via Tanner's Bound**:
If $S \subseteq V$ is non-empty with relative volume $|S|/n \le \alpha$ where $0 < \alpha$,
then $|N(S)| \ge \frac{d^2}{\alpha (d^2 - \lambda^2) + \lambda^2} |S|$.
-/
theorem tanner_small_set_expansion (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S : Finset V) (hS : 0 < S.card) {α : ℝ} (hα : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ α)
    (_hα_pos : 0 < α) :
    ((d : ℝ) ^ 2 / (α * ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) ≤
    ((neighborhood G S).card : ℝ) := by
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  have h_ratio := tanner_expansion_ratio_bound G hreg hn hd S hS
  have h_diff_nonneg : 0 ≤ (d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2 := by
    have := sq_spectralExpansionParameter_le_sq_d G hreg; linarith
  have h_denom_le : ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2 ≤
      α * ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) + (spectralExpansionParameter G) ^ 2 := by
    nlinarith
  have h_denom1_pos : 0 < ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2 := by
    have h_orig := tanner_denominator_pos G hn hd S hS
    have : ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2 =
        ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2 := by ring
    rwa [this] at h_orig
  have h_frac_le : (d : ℝ) ^ 2 / (α * ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) + (spectralExpansionParameter G) ^ 2) ≤
      (d : ℝ) ^ 2 / (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) * ((S.card : ℝ) / (Fintype.card V : ℝ)) + (spectralExpansionParameter G) ^ 2) := by
    have h_denom2_pos : 0 < α * ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) + (spectralExpansionParameter G) ^ 2 :=
      lt_of_lt_of_le h_denom1_pos h_denom_le
    rw [div_le_div_iff₀ h_denom2_pos h_denom1_pos]
    nlinarith
  rw [← le_div_iff₀ hs_pos]
  exact le_trans h_frac_le h_ratio

omit [DecidableEq V] in
/-- Ramanujan spectral parameter squared bound: $\lambda^2 \le 4(d-1)$. -/
theorem ramanujan_sq_spectralExpansionParameter_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hRam : spectralExpansionParameter G ≤ 2 * Real.sqrt ((d : ℝ) - 1)) :
    (spectralExpansionParameter G) ^ 2 ≤ 4 * ((d : ℝ) - 1) := by
  have hd1 : 0 ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := Nat.ofNat_le_cast.mpr hd; linarith
  have h_nonneg := spectralExpansionParameter_nonneg G
  have h_sq : (spectralExpansionParameter G) ^ 2 ≤ (2 * Real.sqrt ((d : ℝ) - 1)) ^ 2 := by nlinarith
  have h_eval : (2 * Real.sqrt ((d : ℝ) - 1)) ^ 2 = 4 * ((d : ℝ) - 1) := by
    rw [mul_pow, Real.sq_sqrt hd1]; ring
  linarith

omit [DecidableEq V] in
/-- Positivity of the Ramanujan denominator for non-empty $S \subseteq V$ and $d \ge 2$. -/
theorem tanner_ramanujan_denominator_pos (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hn : Fintype.card V ≠ 0) (hd : 2 ≤ d) (S : Finset V) (hS : 0 < S.card) :
    0 < (((d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1)) / (Fintype.card V : ℝ)) * (S.card : ℝ) + 4 * ((d : ℝ) - 1) := by
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  have hd_ge : (2 : ℝ) ≤ (d : ℝ) := Nat.ofNat_le_cast.mpr hd
  have h_sq_nonneg : 0 ≤ (d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1) := by
    have : (d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1) = ((d : ℝ) - 2) ^ 2 := by ring
    rw [this]; exact sq_nonneg _
  have : 0 ≤ (((d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1)) / (Fintype.card V : ℝ)) * (S.card : ℝ) := by positivity
  linarith

/--
**Tanner's Expansion Bound for Ramanujan Graphs**:
For a Ramanujan graph where $\lambda(G) \le 2\sqrt{d-1}$ ($d \ge 2$), any non-empty subset $S \subseteq V$ satisfies:
$$|N(S)| \ge \frac{d^2 |S|}{\frac{d^2 - 4(d-1)}{n}|S| + 4(d-1)}$$
-/
theorem tanner_ramanujan_expansion (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 2 ≤ d)
    (hRam : spectralExpansionParameter G ≤ 2 * Real.sqrt ((d : ℝ) - 1))
    (S : Finset V) (hS : 0 < S.card) :
    ((d : ℝ) ^ 2 * (S.card : ℝ)) /
      ((((d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1)) / (Fintype.card V : ℝ)) * (S.card : ℝ) + 4 * ((d : ℝ) - 1)) ≤
    ((neighborhood G S).card : ℝ) := by
  have hd_pos : 0 < d := by linarith
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  have hs_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ S)
  have h_bound := tanner_vertex_expansion_bound G hreg hn hd_pos S hS
  have h_lam_sq_le := ramanujan_sq_spectralExpansionParameter_le G hd hRam
  have h_sub_nonneg : 0 ≤ 1 - (S.card : ℝ) / (Fintype.card V : ℝ) := by
    rw [sub_nonneg]; exact (div_le_one hn_pos).mpr hs_le
  have h_denom_orig : ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2 =
      (d : ℝ) ^ 2 * (S.card : ℝ) / (Fintype.card V : ℝ) + (spectralExpansionParameter G) ^ 2 * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by ring
  have h_denom_ram : (((d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1)) / (Fintype.card V : ℝ)) * (S.card : ℝ) + 4 * ((d : ℝ) - 1) =
      (d : ℝ) ^ 2 * (S.card : ℝ) / (Fintype.card V : ℝ) + (4 * ((d : ℝ) - 1)) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by ring
  have h_denom_le : ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2 ≤
      (((d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1)) / (Fintype.card V : ℝ)) * (S.card : ℝ) + 4 * ((d : ℝ) - 1) := by
    rw [h_denom_orig, h_denom_ram]
    nlinarith
  have h_denom1_pos := tanner_denominator_pos G hn hd_pos S hS
  have h_denom2_pos := tanner_ramanujan_denominator_pos G hn hd S hS
  have h_frac_le : ((d : ℝ) ^ 2 * (S.card : ℝ)) / ((((d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1)) / (Fintype.card V : ℝ)) * (S.card : ℝ) + 4 * ((d : ℝ) - 1)) ≤
      ((d : ℝ) ^ 2 * (S.card : ℝ)) / (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / (Fintype.card V : ℝ) * (S.card : ℝ) + (spectralExpansionParameter G) ^ 2) := by
    rw [div_le_div_iff₀ h_denom2_pos h_denom1_pos]
    exact mul_le_mul_of_nonneg_left h_denom_le (by positivity)
  exact le_trans h_frac_le h_bound

/--
**Tanner's Expansion Bound for Ramanujan Graphs (Factored Form)**:
Expressing the denominator leading coefficient as $((d-2)^2 / n) |S| + 4(d-1)$.
-/
theorem tanner_ramanujan_expansion_factored (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 2 ≤ d)
    (hRam : spectralExpansionParameter G ≤ 2 * Real.sqrt ((d : ℝ) - 1))
    (S : Finset V) (hS : 0 < S.card) :
    ((d : ℝ) ^ 2 * (S.card : ℝ)) /
      ((((d : ℝ) - 2) ^ 2 / (Fintype.card V : ℝ)) * (S.card : ℝ) + 4 * ((d : ℝ) - 1)) ≤
    ((neighborhood G S).card : ℝ) := by
  have : (d : ℝ) ^ 2 - 4 * ((d : ℝ) - 1) = ((d : ℝ) - 2) ^ 2 := by ring
  have h_ram := tanner_ramanujan_expansion G hreg hn hd hRam S hS
  rwa [this] at h_ram

/--
**Tanner Vertex Expansion for Bounded Subsets ($|S| \le n/2$)**:
For any non-empty subset $S \subseteq V$ containing at most half the vertices ($|S| \le n/2$),
$$|N(S)| \ge \frac{2 d^2}{d^2 + \lambda^2} |S|$$
-/
theorem tanner_half_set_expansion (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S : Finset V) (hS : 0 < S.card)
    (hhalf : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    ((2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) ≤
    ((neighborhood G S).card : ℝ) := by
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hd_pos_r : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have h_denom_ne : (d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2 ≠ 0 := by positivity
  have hα : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ (1 / 2 : ℝ) := (div_le_iff₀ hn_pos).mpr (by linarith)
  have h_small := tanner_small_set_expansion G hreg hn hd S hS hα (by norm_num)
  have h_frac_eq : (d : ℝ) ^ 2 / ((1 / 2 : ℝ) * ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) + (spectralExpansionParameter G) ^ 2) =
      (2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2) := by
    have : (1 / 2 : ℝ) * ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) + (spectralExpansionParameter G) ^ 2 =
        ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2) / 2 := by ring
    rw [this]; field_simp [h_denom_ne]
  rwa [h_frac_eq] at h_small

/--
**Tanner Vertex Expansion Ratio for Bounded Subsets ($|S| \le n/2$)**:
$$\frac{|N(S)|}{|S|} \ge \frac{2 d^2}{d^2 + \lambda^2}$$
-/
theorem tanner_half_set_expansion_ratio (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S : Finset V) (hS : 0 < S.card)
    (hhalf : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2) ≤
    ((neighborhood G S).card : ℝ) / (S.card : ℝ) := by
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  exact (le_div_iff₀ hs_pos).mpr (tanner_half_set_expansion G hreg hn hd S hS hhalf)

/--
**Vertex Expansion Difference Bound (Relation to Cheeger Constant)**:
For any non-empty subset $S \subseteq V$ with $|S| \le n/2$,
the vertex expansion margin $|N(S)| - |S|$ satisfies:
$$|N(S)| - |S| \ge \frac{d^2 - \lambda^2}{d^2 + \lambda^2} |S|$$
-/
theorem tanner_vertex_margin_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S : Finset V) (hS : 0 < S.card)
    (hhalf : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) ≤
    ((neighborhood G S).card : ℝ) - (S.card : ℝ) := by
  have h_exp := tanner_half_set_expansion G hreg hn hd S hS hhalf
  have hd_pos_r : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have h_denom_ne : (d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2 ≠ 0 := by positivity
  have h_alg : ((2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) - (S.card : ℝ) =
      (((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) := by
    field_simp [h_denom_ne]; ring
  linarith

/--
**Ramanujan Half-Set Vertex Expansion Bound**:
For a Ramanujan graph ($d \ge 2$, $\lambda \le 2\sqrt{d-1}$) and any non-empty $S$ with $|S| \le n/2$:
$$|N(S)| \ge \frac{2 d^2}{d^2 + 4d - 4} |S|$$
-/
theorem tanner_ramanujan_half_set_expansion (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 2 ≤ d)
    (hRam : spectralExpansionParameter G ≤ 2 * Real.sqrt ((d : ℝ) - 1))
    (S : Finset V) (hS : 0 < S.card)
    (hhalf : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    ((2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + 4 * (d : ℝ) - 4)) * (S.card : ℝ) ≤
    ((neighborhood G S).card : ℝ) := by
  have hd_pos : 0 < d := by linarith
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  have h_half_exp := tanner_half_set_expansion G hreg hn hd_pos S hS hhalf
  have h_lam_sq_le := ramanujan_sq_spectralExpansionParameter_le G hd hRam
  have hd_ge : (2 : ℝ) ≤ (d : ℝ) := Nat.ofNat_le_cast.mpr hd
  have h_denom1_pos : 0 < (d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2 := by positivity
  have h_denom2_pos : 0 < (d : ℝ) ^ 2 + 4 * (d : ℝ) - 4 := by
    have : (d : ℝ) ^ 2 + 4 * (d : ℝ) - 4 = ((d : ℝ) + 2) ^ 2 - 8 := by ring
    nlinarith
  have h_frac_le : (2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + 4 * (d : ℝ) - 4) ≤
      (2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2) := by
    rw [div_le_div_iff₀ h_denom2_pos h_denom1_pos]
    nlinarith
  have h_mul_le : ((2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + 4 * (d : ℝ) - 4)) * (S.card : ℝ) ≤
      ((2 * (d : ℝ) ^ 2) / ((d : ℝ) ^ 2 + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) := by
    nlinarith
  exact le_trans h_mul_le h_half_exp

end TannerExpansion
