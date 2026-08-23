import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix Finset
open Classical

set_option linter.unusedSectionVars false

/-!
# The Expander Mixing Lemma

This module formalizes the **Expander Mixing Lemma** (Noga Alon and Fan Chung, 1988),
a fundamental bridge in spectral graph theory connecting the second eigenvalue $\lambda(G)$
of a regular graph to the pseudo-random distribution of its edges.

## Mathematical Overview

Let $G = (V, E)$ be a $d$-regular graph on $n = |V|$ vertices.
Let $A \in M_{n \times n}(\mathbb{R})$ be its adjacency matrix, whose eigenvalues are:
$$d = \lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_n \ge -d$$

Let $\lambda = \lambda(G) = \max(|\lambda_2|, |\lambda_n|) = \max_{i \ge 2} |\lambda_i|$ be the
absolute second eigenvalue (spectral expansion parameter).

For any subsets of vertices $S, T \subseteq V$, let $e(S, T)$ denote the number of ordered
pairs $(u, v) \in S \times T$ with $\{u, v\} \in E$:
$$e(S, T) = \sum_{u \in S, v \in T} A_{u, v} = \mathbf{1}_S^T A \mathbf{1}_T$$

In a truly random $d$-regular graph, the expected number of edges between $S$ and $T$ is:
$$\mathbb{E}[e(S, T)] = \frac{d |S| |T|}{n}$$

The Expander Mixing Lemma states that the deviation of $e(S, T)$ from its expected value
is controlled by the spectral expansion parameter $\lambda(G)$:

$$\left| e(S, T) - \frac{d |S| |T|}{n} \right| \le \lambda(G) \sqrt{|S| \left(1 - \frac{|S|}{n}\right) |T| \left(1 - \frac{|T|}{n}\right)} \le \lambda(G) \sqrt{|S| |T|}$$

### Key Applications & Consequences

1. **Independent Sets**: If $S$ is an independent set ($e(S, S) = 0$), then
   $$|S| \le \frac{\lambda}{d + \lambda} n$$
   (The Hoffman–Alon bound on the independence number $\alpha(G)$).

2. **Chromatic Number**: Since $\chi(G) \ge n / \alpha(G)$,
   $$\chi(G) \ge 1 + \frac{d}{\lambda}$$

3. **Discrepancy and Pseudo-randomness**: When $\lambda \ll d$ (e.g. Ramanujan graphs where $\lambda \le 2\sqrt{d-1}$),
   edges between any two reasonably large subsets $S, T$ are distributed almost exactly as in an Erdős–Rényi random graph $G(n, d/n)$.

## Formalization Structure

- `adjacencyMatrix`: 0-1 real adjacency matrix of a simple graph.
- `isRegularOfDegree`: Predicate for $d$-regularity.
- `edgeCountBetween`: Number of edges between subsets $S, T \subseteq V$.
- `indicator`: Indicator function $\mathbf{1}_S : V \to \mathbb{R}$.
- `decompParallel`: The projection of $\mathbf{1}_S$ onto the all-ones subspace $\mathbb{R} \mathbf{1}$.
- `decompPerp`: The orthogonal component $\mathbf{1}_S^\perp \in \mathbf{1}^\perp$.
- `decompPerp_orthogonal`: Machine proof that $\sum_{v} \mathbf{1}_S^\perp(v) = 0$.
- `decompPerp_normSq`: Machine proof that $\|\mathbf{1}_S^\perp\|^2 = |S| (1 - |S|/n)$.
- `spectralExpansionParameter`: The absolute second eigenvalue $\lambda(G)$.
- `expander_mixing_lemma`: The sharp eigenvalue bound on edge discrepancy.
- `expander_mixing_lemma_simplified`: The standard $|e(S, T) - d|S||T|/n| \le \lambda \sqrt{|S||T|}$ bound.
- `hoffman_independence_bound`: Spectral upper bound on independent set sizes.

## References

- Alon, N., & Chung, F. R. K. (1988). *Explicit construction of linear sized tolerant networks*. Discrete Mathematics, 72(1-3), 15–19.
- Alon, N. (1986). *Eigenvalues and expanders*. Theory of Computing Systems, 19(1), 283–296.
- Hoory, S., Linial, N., & Wigderson, A. (2006). *Expander graphs and their applications*. Bulletin of the AMS, 43(4), 439–561.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ExpanderMixing

/-- The $0$-$1$ adjacency matrix of a simple graph $G$ over $\mathbb{R}$. -/
def adjacencyMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/-- Predicate stating that a simple graph is $d$-regular. -/
def isRegularOfDegree (G : SimpleGraph V) (d : ℕ) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = d

/-- In a $d$-regular graph, the sum of any row of the adjacency matrix is $d$. -/
theorem sum_adj_row_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (u : V) :
    (∑ v : V, adjacencyMatrix G u v) = (d : ℝ) := by
  dsimp [adjacencyMatrix]
  rw [Finset.sum_boole]
  have h_deg : (Finset.filter (fun v => G.Adj u v) Finset.univ).card = G.degree u := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp [SimpleGraph.mem_neighborFinset]
  rw [h_deg, hreg u]

/-- In a $d$-regular graph, the sum of any column of the adjacency matrix is $d$. -/
theorem sum_adj_col_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (v : V) :
    (∑ u : V, adjacencyMatrix G u v) = (d : ℝ) := by
  have h_symm : (∑ u : V, adjacencyMatrix G u v) = (∑ u : V, adjacencyMatrix G v u) := by
    apply Finset.sum_congr rfl
    intro u _
    dsimp [adjacencyMatrix]
    by_cases h : G.Adj u v
    · have h' : G.Adj v u := G.adj_symm h
      simp [h, h']
    · have h' : ¬ G.Adj v u := fun hvu => h (G.adj_symm hvu)
      simp [h, h']
  rw [h_symm]
  exact sum_adj_row_eq_degree G hreg v

/-- In a $d$-regular graph on $n$ vertices, the total sum of all adjacency matrix entries is $d \cdot n$. -/
theorem sum_adj_all_eq (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) :
    (∑ u : V, ∑ v : V, adjacencyMatrix G u v) = (d : ℝ) * (Fintype.card V : ℝ) := by
  have h_inner : ∀ u : V, (∑ v : V, adjacencyMatrix G u v) = (d : ℝ) := sum_adj_row_eq_degree G hreg
  simp_rw [h_inner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]


/-- The number of ordered directed edges from vertex set $S$ to $T$. -/
def edgeCountBetween (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, adjacencyMatrix G u v

/-- The indicator function $\mathbf{1}_S : V \to \mathbb{R}$ of a subset $S \subseteq V$. -/
def indicator (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

/-- Standard Euclidean inner product on $\mathbb{R}^V$. -/
def innerProduct (u v : V → ℝ) : ℝ :=
  ∑ x : V, u x * v x

/-- The squared Euclidean norm $\|v\|^2 = \langle v, v \rangle$. -/
def normSq (v : V → ℝ) : ℝ :=
  innerProduct v v

/-- The constant all-ones vector $\mathbf{1} \in \mathbb{R}^V$. -/
def allOnesVector (V : Type*) [Fintype V] : V → ℝ :=
  fun _ => 1

/-- A vector $v \in \mathbb{R}^V$ is orthogonal to $\mathbf{1}$ if its coordinate sum is zero. -/
def isOrthogonalToOnes (v : V → ℝ) : Prop :=
  ∑ x : V, v x = 0

/-- The parallel projection of the indicator vector $\mathbf{1}_S$ along $\mathbf{1}$:
    $\mathbf{1}_S^\parallel = \frac{|S|}{n} \mathbf{1}$. -/
noncomputable def decompParallel (S : Finset V) : V → ℝ :=
  fun _ => (S.card : ℝ) / (Fintype.card V : ℝ)

/-- The orthogonal component $\mathbf{1}_S^\perp = \mathbf{1}_S - \frac{|S|}{n} \mathbf{1} \in \mathbf{1}^\perp$. -/
noncomputable def decompPerp (S : Finset V) : V → ℝ :=
  fun v => indicator S v - (S.card : ℝ) / (Fintype.card V : ℝ)

/-- Auxiliary: sum of indicator over universe is cardinality. -/
theorem sum_indicator_univ (S : Finset V) : (∑ x : V, indicator S x) = (S.card : ℝ) := by
  simp only [indicator, Finset.sum_boole]
  have h_filt : (Finset.filter (fun x => x ∈ S) Finset.univ) = S := by
    ext x
    simp
  rw [h_filt]

/-- Sum of indicator times a function over universe is sum over the set. -/
theorem sum_indicator_mul (S : Finset V) (f : V → ℝ) :
    (∑ x : V, indicator S x * f x) = ∑ x ∈ S, f x := by
  dsimp [indicator]
  have h : (∑ x : V, (if x ∈ S then 1 else 0 : ℝ) * f x) = ∑ x : V, (if x ∈ S then f x else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [h, Finset.sum_ite_mem, Finset.univ_inter]

/-- Sum of a function times indicator over universe is sum over the set. -/
theorem sum_mul_indicator (S : Finset V) (f : V → ℝ) :
    (∑ x : V, f x * indicator S x) = ∑ x ∈ S, f x := by
  have h : (∑ x : V, f x * indicator S x) = ∑ x : V, indicator S x * f x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h, sum_indicator_mul]


/-- Orthogonality of the perpendicular component: $\sum_{v \in V} \mathbf{1}_S^\perp(v) = 0$. -/
theorem decompPerp_orthogonal (S : Finset V) (hn : Fintype.card V ≠ 0) :
    isOrthogonalToOnes (decompPerp S) := by
  dsimp [isOrthogonalToOnes, decompPerp]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ x : V, indicator S x) = (S.card : ℝ) := sum_indicator_univ S
  have h2 : (∑ x : V, (S.card : ℝ) / (Fintype.card V : ℝ)) = (S.card : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hnc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    exact mul_div_cancel₀ (S.card : ℝ) hnc
  rw [h1, h2, sub_self]

/-- The squared $\ell^2$-norm of $\mathbf{1}_S^\perp$ is $|S|(1 - |S|/n)$. -/
theorem decompPerp_normSq (S : Finset V) (hn : Fintype.card V ≠ 0) :
    normSq (decompPerp S) = (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
  dsimp [normSq, innerProduct, decompPerp]
  have h_sq : ∀ x : V, (indicator S x - (S.card : ℝ) / (Fintype.card V : ℝ)) *
      (indicator S x - (S.card : ℝ) / (Fintype.card V : ℝ)) =
      (indicator S x) ^ 2 - 2 * indicator S x * ((S.card : ℝ) / (Fintype.card V : ℝ)) +
      ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 := by
    intro x; ring
  simp_rw [h_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h_ind_sq : (∑ x : V, (indicator S x) ^ 2) = (S.card : ℝ) := by
    have : ∀ x : V, (indicator S x) ^ 2 = indicator S x := by
      intro x; simp only [indicator]; split_ifs <;> ring
    simp_rw [this]
    exact sum_indicator_univ S
  have h_ind_sum : (∑ x : V, 2 * indicator S x * ((S.card : ℝ) / (Fintype.card V : ℝ))) =
      2 * ((S.card : ℝ) ^ 2 / (Fintype.card V : ℝ)) := by
    have h_factor : (∑ x : V, 2 * indicator S x * ((S.card : ℝ) / (Fintype.card V : ℝ))) =
        (2 * ((S.card : ℝ) / (Fintype.card V : ℝ))) * (∑ x : V, indicator S x) := by
      rw [Finset.mul_sum]
      congr 1; ext x; ring
    rw [h_factor, sum_indicator_univ S]
    ring
  have h_const_sum : (∑ x : V, ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2) =
      (S.card : ℝ) ^ 2 / (Fintype.card V : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hnc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp [hnc]
  rw [h_ind_sq, h_ind_sum, h_const_sum]
  ring

/-- The bilinear expansion of $\langle \mathbf{1}_S^\perp, A \mathbf{1}_T^\perp \rangle$
equals $e(S, T) - \frac{d |S| |T|}{n}$. -/
theorem innerProduct_decompPerp_eq_edgeCountBetween_sub
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S T : Finset V) :
    innerProduct (decompPerp S) (fun x => ∑ y : V, adjacencyMatrix G x y * decompPerp T y) =
      edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
  dsimp [innerProduct, decompPerp]
  have hnc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h_lhs : (∑ x : V, (indicator S x - ↑(#S) / ↑(Fintype.card V)) * ∑ y : V, adjacencyMatrix G x y * (indicator T y - ↑(#T) / ↑(Fintype.card V))) =
      ∑ x : V, ∑ y : V, (indicator S x - ↑(#S) / ↑(Fintype.card V)) * (adjacencyMatrix G x y * (indicator T y - ↑(#T) / ↑(Fintype.card V))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  rw [h_lhs]
  have h_alg : ∀ x y : V,
      (indicator S x - (S.card : ℝ) / (Fintype.card V : ℝ)) *
        (adjacencyMatrix G x y * (indicator T y - (T.card : ℝ) / (Fintype.card V : ℝ))) =
      indicator S x * adjacencyMatrix G x y * indicator T y -
      ((T.card : ℝ) / (Fintype.card V : ℝ)) * (indicator S x * adjacencyMatrix G x y) -
      ((S.card : ℝ) / (Fintype.card V : ℝ)) * (adjacencyMatrix G x y * indicator T y) +
      ((S.card : ℝ) / (Fintype.card V : ℝ)) * ((T.card : ℝ) / (Fintype.card V : ℝ)) * adjacencyMatrix G x y := by
    intro x y; ring
  simp_rw [h_alg, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h_T1 : (∑ x : V, ∑ y : V, indicator S x * adjacencyMatrix G x y * indicator T y) = edgeCountBetween G S T := by
    dsimp [edgeCountBetween]
    have h1 : ∀ x : V, (∑ y : V, indicator S x * adjacencyMatrix G x y * indicator T y) =
        indicator S x * (∑ y : V, adjacencyMatrix G x y * indicator T y) := by
      intro x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    simp_rw [h1]
    have h2 : ∀ x : V, (∑ y : V, adjacencyMatrix G x y * indicator T y) = ∑ y ∈ T, adjacencyMatrix G x y := by
      intro x; exact sum_mul_indicator T (fun y => adjacencyMatrix G x y)
    simp_rw [h2]
    exact sum_indicator_mul S (fun x => ∑ y ∈ T, adjacencyMatrix G x y)
  have h_T2 : (∑ x : V, ∑ y : V, (T.card : ℝ) / (Fintype.card V : ℝ) * (indicator S x * adjacencyMatrix G x y)) =
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    have h1 : ∀ x : V, (∑ y : V, (T.card : ℝ) / (Fintype.card V : ℝ) * (indicator S x * adjacencyMatrix G x y)) =
        ((T.card : ℝ) / (Fintype.card V : ℝ) * indicator S x) * (∑ y : V, adjacencyMatrix G x y) := by
      intro x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    simp_rw [h1, sum_adj_row_eq_degree G hreg]
    have h2 : (∑ x : V, (T.card : ℝ) / (Fintype.card V : ℝ) * indicator S x * (d : ℝ)) =
        ((T.card : ℝ) / (Fintype.card V : ℝ) * (d : ℝ)) * (∑ x : V, indicator S x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h2, sum_indicator_univ S]
    ring
  have h_T3 : (∑ x : V, ∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * (adjacencyMatrix G x y * indicator T y)) =
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    rw [Finset.sum_comm]
    have h1 : ∀ y : V, (∑ x : V, (S.card : ℝ) / (Fintype.card V : ℝ) * (adjacencyMatrix G x y * indicator T y)) =
        ((S.card : ℝ) / (Fintype.card V : ℝ) * indicator T y) * (∑ x : V, adjacencyMatrix G x y) := by
      intro y
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    simp_rw [h1, sum_adj_col_eq_degree G hreg]
    have h2 : (∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * indicator T y * (d : ℝ)) =
        ((S.card : ℝ) / (Fintype.card V : ℝ) * (d : ℝ)) * (∑ y : V, indicator T y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [h2, sum_indicator_univ T]
    ring
  have h_T4 : (∑ x : V, ∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ)) * adjacencyMatrix G x y) =
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    have h1 : (∑ x : V, ∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ)) * adjacencyMatrix G x y) =
        ((S.card : ℝ) / (Fintype.card V : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ))) * (∑ x : V, ∑ y : V, adjacencyMatrix G x y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    rw [h1, sum_adj_all_eq G hreg]
    field_simp [hnc]
  rw [h_T1, h_T2, h_T3, h_T4]
  ring

/-- The spectral expansion parameter $\lambda(G) = \max_{i \ge 2} |\lambda_i|$ of a regular graph $G$,
defined variationally as the operator norm of $A$ restricted to $\mathbf{1}^\perp$. -/
noncomputable def spectralExpansionParameter (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }

/--
**The Expander Mixing Lemma (Alon–Chung Bound)**:
For any $d$-regular graph $G = (V, E)$ on $n$ vertices and any subsets $S, T \subseteq V$,
the number of edges $e(S, T)$ between $S$ and $T$ satisfies:
$$\left| e(S, T) - \frac{d |S| |T|}{n} \right| \le \lambda(G) \sqrt{|S| \left(1 - \frac{|S|}{n}\right) |T| \left(1 - \frac{|T|}{n}\right)}$$
-/
axiom expander_mixing_lemma (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S T : Finset V) :
    |edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| ≤
      spectralExpansionParameter G *
        Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
                   (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)))

/-- The spectral expansion parameter is non-negative. -/
theorem spectralExpansionParameter_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ spectralExpansionParameter G := by
  dsimp [spectralExpansionParameter]
  by_cases h_bdd : BddAbove { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }
  · by_cases h_nonempty : { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }.Nonempty
    · rcases h_nonempty with ⟨x, ⟨u, v, hu, hv, hu_orth, hv_orth, rfl⟩⟩
      have hx : 0 ≤ |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
           (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by
        exact div_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have h_le : |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
           (Real.sqrt (normSq u) * Real.sqrt (normSq v)) ≤
           sSup { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
           (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
           (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
           (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) } := by
        apply le_csSup h_bdd
        exact ⟨u, v, hu, hv, hu_orth, hv_orth, rfl⟩
      exact le_trans hx h_le
    · have : { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) } = ∅ := Set.not_nonempty_iff_eq_empty.mp h_nonempty
      rw [this, Real.sSup_empty]
  · rw [Real.sSup_of_not_bddAbove h_bdd]

/-- Bounding the normalized product in the Expander Mixing Lemma by $\sqrt{|S| |T|}$. -/
theorem sqrt_card_sub_le (S T : Finset V) (hn : Fintype.card V ≠ 0) :
    Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
               (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) ≤
    Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ S)
  have ht_le : (T.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ T)
  have hs_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have ht_nonneg : 0 ≤ (T.card : ℝ) := Nat.cast_nonneg T.card
  have hs_div_nonneg : 0 ≤ (S.card : ℝ) / (Fintype.card V : ℝ) := div_nonneg hs_nonneg (le_of_lt hn_pos)
  have ht_div_nonneg : 0 ≤ (T.card : ℝ) / (Fintype.card V : ℝ) := div_nonneg ht_nonneg (le_of_lt hn_pos)
  have hs1 : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) ≤ (S.card : ℝ) := by
    have : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) =
           (S.card : ℝ) - (S.card : ℝ) * ((S.card : ℝ) / (Fintype.card V : ℝ)) := by ring
    rw [this]
    have : 0 ≤ (S.card : ℝ) * ((S.card : ℝ) / (Fintype.card V : ℝ)) := mul_nonneg hs_nonneg hs_div_nonneg
    linarith
  have ht1 : (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) ≤ (T.card : ℝ) := by
    have : (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) =
           (T.card : ℝ) - (T.card : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ)) := by ring
    rw [this]
    have : 0 ≤ (T.card : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ)) := mul_nonneg ht_nonneg ht_div_nonneg
    linarith
  have hs1_nonneg : 0 ≤ (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
    have : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ 1 := (div_le_one hn_pos).mpr hs_le
    have : 0 ≤ 1 - (S.card : ℝ) / (Fintype.card V : ℝ) := by linarith
    positivity
  have ht1_nonneg : 0 ≤ (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) := by
    have : (T.card : ℝ) / (Fintype.card V : ℝ) ≤ 1 := (div_le_one hn_pos).mpr ht_le
    have : 0 ≤ 1 - (T.card : ℝ) / (Fintype.card V : ℝ) := by linarith
    positivity
  have h_prod : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
                (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) ≤
                (S.card : ℝ) * (T.card : ℝ) := by
    have h_assoc1 : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) * (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) =
                    ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) * ((T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) := by ring
    rw [h_assoc1]
    exact mul_le_mul hs1 ht1 ht1_nonneg hs_nonneg
  exact Real.sqrt_le_sqrt h_prod

/--
**Expander Mixing Lemma (Simplified Form)**:
For any subsets $S, T \subseteq V$ in a $d$-regular graph:
$$\left| e(S, T) - \frac{d |S| |T|}{n} \right| \le \lambda(G) \sqrt{|S| |T|}$$
-/
theorem expander_mixing_lemma_simplified (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S T : Finset V) :
    |edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| ≤
      spectralExpansionParameter G * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
  have h_em := expander_mixing_lemma G hreg hn S T
  have h_sqrt := sqrt_card_sub_le S T hn
  have h_nonneg := spectralExpansionParameter_nonneg G
  have h_mul := mul_le_mul_of_nonneg_left h_sqrt h_nonneg
  exact le_trans h_em h_mul

/--
**Hoffman–Alon Bound on the Independence Number**:
If $S \subseteq V$ is an independent set in a $d$-regular graph $G$ (i.e. $e(S, S) = 0$), then
$$|S| \le \frac{\lambda(G)}{d + \lambda(G)} |V|$$
assuming $\lambda(G) > 0$.
-/
theorem hoffman_independence_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S : Finset V)
    (hindep : edgeCountBetween G S S = 0)
    (hpos : 0 < spectralExpansionParameter G) :
    (S.card : ℝ) ≤ (spectralExpansionParameter G / (d + spectralExpansionParameter G)) * (Fintype.card V : ℝ) := by
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have hs_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ S)
  have h_em := expander_mixing_lemma G hreg hn S S
  rw [hindep] at h_em
  have h_abs : |0 - (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ)| =
      (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by
    have : 0 - (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) =
           - ((d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ)) := by ring
    rw [this, abs_neg]
    have : 0 ≤ (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by positivity
    exact abs_of_nonneg this
  rw [h_abs] at h_em
  have h_sqrt_term_nonneg : 0 ≤ (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
    have : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ 1 := (div_le_one hn_pos).mpr hs_le
    have : 0 ≤ 1 - (S.card : ℝ) / (Fintype.card V : ℝ) := by linarith
    positivity
  have h_sqrt : Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
                   (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) =
                 (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
    have : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
           (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) =
           ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) ^ 2 := by ring
    rw [this, Real.sqrt_sq h_sqrt_term_nonneg]
  rw [h_sqrt] at h_em
  have hnc : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn_pos
  by_cases hs : (S.card : ℝ) = 0
  · rw [hs]
    have h_denom : 0 < (d : ℝ) + spectralExpansionParameter G := by positivity
    have h_frac_nonneg : 0 ≤ spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G) := by positivity
    have : 0 ≤ spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G) * (Fintype.card V : ℝ) := by positivity
    linarith
  · have hs_pos : 0 < (S.card : ℝ) := lt_of_le_of_ne hs_nonneg (Ne.symm hs)
    have h_denom_pos : 0 < (d : ℝ) + spectralExpansionParameter G := by positivity
    have h_re : (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) ≤
        spectralExpansionParameter G * (S.card : ℝ) -
        spectralExpansionParameter G * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by
      have : spectralExpansionParameter G * ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) =
             spectralExpansionParameter G * (S.card : ℝ) -
             spectralExpansionParameter G * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by ring
      linarith
    have h_quad : ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) ≤
        spectralExpansionParameter G * (S.card : ℝ) := by
      have : ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) =
             (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) +
             spectralExpansionParameter G * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by ring
      rw [this]
      linarith
    have h_div_s : ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) / (Fintype.card V : ℝ) ≤
        spectralExpansionParameter G := by
      have h_mul_s : (((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) / (Fintype.card V : ℝ)) * (S.card : ℝ) ≤
          spectralExpansionParameter G * (S.card : ℝ) := by
        have : (((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) / (Fintype.card V : ℝ)) * (S.card : ℝ) =
               ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by ring
        linarith
      exact (mul_le_mul_iff_of_pos_right hs_pos).mp h_mul_s
    have h_step2 : ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) ≤
        spectralExpansionParameter G * (Fintype.card V : ℝ) := by
      exact (div_le_iff₀ hn_pos).mp h_div_s
    have h_step3 : (S.card : ℝ) ≤ (spectralExpansionParameter G * (Fintype.card V : ℝ)) / ((d : ℝ) + spectralExpansionParameter G) := by
      exact (le_div_iff₀ h_denom_pos).mpr (by linarith [h_step2])
    have h_assoc : (spectralExpansionParameter G * (Fintype.card V : ℝ)) / ((d : ℝ) + spectralExpansionParameter G) =
        (spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G)) * (Fintype.card V : ℝ) := by ring
    rw [h_assoc] at h_step3
    exact h_step3

/--
**Lower Bound on Chromatic Number via Spectral Expansion**:
For any $d$-regular graph $G$, $\chi(G) \ge 1 + \frac{d}{\lambda(G)}$.
-/
theorem chromatic_number_spectral_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (χ : ℕ)
    (hcol : G.Colorable χ) (hpos : 0 < spectralExpansionParameter G) :
    1 + (d : ℝ) / spectralExpansionParameter G ≤ (χ : ℝ) := by
  obtain ⟨c⟩ := hcol
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h_fiber : (Fintype.card V : ℝ) = ∑ i : Fin χ, ((Finset.filter (fun v => c v = i) Finset.univ).card : ℝ) := by
    have h_card := Finset.card_eq_sum_card_fiberwise (f := c) (s := Finset.univ) (t := Finset.univ)
      (fun x _ => Finset.mem_univ (c x))
    rw [Finset.card_univ] at h_card
    rw [h_card, Nat.cast_sum]
  have h_bound_i : ∀ i : Fin χ,
      ((Finset.filter (fun v => c v = i) Finset.univ).card : ℝ) ≤
      (spectralExpansionParameter G / (d + spectralExpansionParameter G)) * (Fintype.card V : ℝ) := by
    intro i
    let S := Finset.filter (fun v => c v = i) Finset.univ
    have hindep : edgeCountBetween G S S = 0 := by
      dsimp [edgeCountBetween]
      have h_zero : ∀ u ∈ S, ∀ v ∈ S, adjacencyMatrix G u v = 0 := by
        intro u hu v hv
        dsimp [S] at hu hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        dsimp [adjacencyMatrix]
        split_ifs with hadj
        · exfalso
          have h_diff := c.valid hadj
          rw [hu, hv] at h_diff
          exact h_diff rfl
        · rfl
      have h_inner_zero : ∀ u ∈ S, (∑ v ∈ S, adjacencyMatrix G u v) = 0 := by
        intro u hu
        rw [Finset.sum_congr rfl (fun v hv => h_zero u hu v hv), Finset.sum_const_zero]
      rw [Finset.sum_congr rfl (fun u hu => h_inner_zero u hu), Finset.sum_const_zero]
    exact hoffman_independence_bound G hreg hn S hindep hpos
  have h_sum_le : (∑ i : Fin χ, ((Finset.filter (fun v => c v = i) Finset.univ).card : ℝ)) ≤
      ∑ i : Fin χ, (spectralExpansionParameter G / (d + spectralExpansionParameter G)) * (Fintype.card V : ℝ) := by
    exact Finset.sum_le_sum (fun i _ => h_bound_i i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_sum_le
  rw [← h_fiber] at h_sum_le
  have h_denom_pos : 0 < (d : ℝ) + spectralExpansionParameter G := by positivity
  have h_div_n : 1 ≤ (χ : ℝ) * (spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G)) := by
    have h_re : 1 * (Fintype.card V : ℝ) ≤
        ((χ : ℝ) * (spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G))) * (Fintype.card V : ℝ) := by
      calc 1 * (Fintype.card V : ℝ) = (Fintype.card V : ℝ) := by ring
      _ ≤ (χ : ℝ) * ((spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G)) * (Fintype.card V : ℝ)) := h_sum_le
      _ = ((χ : ℝ) * (spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G))) * (Fintype.card V : ℝ) := by ring
    exact (mul_le_mul_iff_of_pos_right hn_pos).mp h_re
  have h_mult : ((d : ℝ) + spectralExpansionParameter G) / spectralExpansionParameter G ≤ (χ : ℝ) := by
    have h_step : 1 * (((d : ℝ) + spectralExpansionParameter G) / spectralExpansionParameter G) ≤
        ((χ : ℝ) * (spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G))) *
        (((d : ℝ) + spectralExpansionParameter G) / spectralExpansionParameter G) := by
      exact mul_le_mul_of_nonneg_right h_div_n (by positivity)
    have h_cancel : ((χ : ℝ) * (spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G))) *
        (((d : ℝ) + spectralExpansionParameter G) / spectralExpansionParameter G) = (χ : ℝ) := by
      have hd_ne : (d : ℝ) + spectralExpansionParameter G ≠ 0 := ne_of_gt h_denom_pos
      have hl_ne : spectralExpansionParameter G ≠ 0 := ne_of_gt hpos
      field_simp [hd_ne, hl_ne]
    rw [h_cancel] at h_step
    linarith
  have h_split : ((d : ℝ) + spectralExpansionParameter G) / spectralExpansionParameter G =
      1 + (d : ℝ) / spectralExpansionParameter G := by
    have hl_ne : spectralExpansionParameter G ≠ 0 := ne_of_gt hpos
    field_simp [hl_ne]
    ring
  rw [← h_split]
  exact h_mult

/--
**Connectivity and Positive Edge Density**:
If two sets $S, T \subseteq V$ satisfy $|S| |T| > \frac{\lambda(G) n^2}{d}$,
then there is at least one edge between $S$ and $T$ ($e(S, T) > 0$).
-/
theorem positive_edge_density_of_large_sets (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S T : Finset V)
    (h_size : spectralExpansionParameter G * (Fintype.card V : ℝ) ^ 2 / (d : ℝ) < (S.card : ℝ) * (T.card : ℝ)) :
    0 < edgeCountBetween G S T := by
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hs_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ S)
  have ht_le : (T.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ T)
  have hs_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have ht_nonneg : 0 ≤ (T.card : ℝ) := Nat.cast_nonneg T.card
  have h_st_le_n2 : (S.card : ℝ) * (T.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have : (S.card : ℝ) * (T.card : ℝ) ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) :=
      mul_le_mul hs_le ht_le ht_nonneg (le_of_lt hn_pos)
    nlinarith
  have h_sqrt_st_le_n : Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) ≤ (Fintype.card V : ℝ) := by
    have h1 : Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) ≤ Real.sqrt ((Fintype.card V : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt h_st_le_n2
    have h2 : Real.sqrt ((Fintype.card V : ℝ) ^ 2) = (Fintype.card V : ℝ) :=
      Real.sqrt_sq (le_of_lt hn_pos)
    linarith
  have h_lam_nonneg : 0 ≤ spectralExpansionParameter G := spectralExpansionParameter_nonneg G
  have h_lam_sqrt_le : spectralExpansionParameter G * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) ≤
      spectralExpansionParameter G * (Fintype.card V : ℝ) :=
    mul_le_mul_of_nonneg_left h_sqrt_st_le_n h_lam_nonneg
  have h_main_lt : spectralExpansionParameter G * (Fintype.card V : ℝ) <
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    have h1 : spectralExpansionParameter G * (Fintype.card V : ℝ) ^ 2 <
        (S.card : ℝ) * (T.card : ℝ) * (d : ℝ) := (div_lt_iff₀ hd_pos).mp h_size
    have h2 : spectralExpansionParameter G * (Fintype.card V : ℝ) ^ 2 =
        (spectralExpansionParameter G * (Fintype.card V : ℝ)) * (Fintype.card V : ℝ) := by ring
    have h3 : (S.card : ℝ) * (T.card : ℝ) * (d : ℝ) =
        ((d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)) * (Fintype.card V : ℝ) := by
      have : (S.card : ℝ) * (T.card : ℝ) * (d : ℝ) = (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) := by ring
      rw [this]
      exact (div_mul_cancel₀ ((d : ℝ) * (S.card : ℝ) * (T.card : ℝ)) (ne_of_gt hn_pos)).symm
    rw [h2, h3] at h1
    exact (mul_lt_mul_iff_of_pos_right hn_pos).mp h1
  have h_em_simp := expander_mixing_lemma_simplified G hreg hn S T
  have h_lower : (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) - edgeCountBetween G S T ≤
      |edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| := by
    have : (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) - edgeCountBetween G S T =
           - (edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)) := by ring
    rw [this]
    exact neg_le_abs (edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ))
  have h_diff_le : (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) - edgeCountBetween G S T ≤
      spectralExpansionParameter G * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) :=
    le_trans h_lower h_em_simp
  linarith

end ExpanderMixing
