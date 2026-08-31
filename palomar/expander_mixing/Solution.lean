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
  have : (Finset.filter (G.Adj u) Finset.univ) = G.neighborFinset u := by
    ext; simp [SimpleGraph.mem_neighborFinset]
  simp [adjacencyMatrix, Finset.sum_boole, this, SimpleGraph.card_neighborFinset_eq_degree, hreg u]

/-- In a $d$-regular graph, the sum of any column of the adjacency matrix is $d$. -/
theorem sum_adj_col_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (v : V) :
    (∑ u : V, adjacencyMatrix G u v) = (d : ℝ) := by
  simp_rw [adjacencyMatrix, G.adj_comm]
  exact sum_adj_row_eq_degree G hreg v

/-- In a $d$-regular graph on $n$ vertices, the total sum of all adjacency matrix entries is $d \cdot n$. -/
theorem sum_adj_all_eq (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) :
    (∑ u : V, ∑ v : V, adjacencyMatrix G u v) = (d : ℝ) * (Fintype.card V : ℝ) := by
  simp [sum_adj_row_eq_degree G hreg, mul_comm]

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
  simp [indicator]

/-- Sum of indicator times a function over universe is sum over the set. -/
theorem sum_indicator_mul (S : Finset V) (f : V → ℝ) :
    (∑ x : V, indicator S x * f x) = ∑ x ∈ S, f x := by
  simp [indicator, ite_mul]

/-- Sum of a function times indicator over universe is sum over the set. -/
theorem sum_mul_indicator (S : Finset V) (f : V → ℝ) :
    (∑ x : V, f x * indicator S x) = ∑ x ∈ S, f x := by
  simp [indicator, mul_ite]

/-- Orthogonality of the perpendicular component: $\sum_{v \in V} \mathbf{1}_S^\perp(v) = 0$. -/
theorem decompPerp_orthogonal (S : Finset V) (hn : Fintype.card V ≠ 0) :
    isOrthogonalToOnes (decompPerp S) := by
  dsimp [isOrthogonalToOnes, decompPerp]
  have : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp [Finset.sum_sub_distrib, sum_indicator_univ, mul_div_cancel₀ _ this]

/-- The squared $\ell^2$-norm of $\mathbf{1}_S^\perp$ is $|S|(1 - |S|/n)$. -/
theorem decompPerp_normSq (S : Finset V) (hn : Fintype.card V ≠ 0) :
    normSq (decompPerp S) = (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
  dsimp [normSq, innerProduct, decompPerp]
  have hnc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h_alg : ∀ x : V, (indicator S x - (S.card : ℝ) / (Fintype.card V : ℝ)) *
      (indicator S x - (S.card : ℝ) / (Fintype.card V : ℝ)) =
      indicator S x - 2 * ((S.card : ℝ) / (Fintype.card V : ℝ)) * indicator S x +
      ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 := by
    intro x; simp [indicator]; split_ifs <;> ring
  simp_rw [h_alg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
           ← Finset.mul_sum, sum_indicator_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card V : ℝ) * ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 =
      (S.card : ℝ) * ((S.card : ℝ) / (Fintype.card V : ℝ)) := by
    rw [sq, ← mul_assoc, mul_div_cancel₀ _ hnc]
  rw [this]
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
    simp_rw [Finset.mul_sum]
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
      intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    simp_rw [h1, sum_mul_indicator, sum_indicator_mul]
  have h_T2 : (∑ x : V, ∑ y : V, (T.card : ℝ) / (Fintype.card V : ℝ) * (indicator S x * adjacencyMatrix G x y)) =
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    have h1 : ∀ x : V, (∑ y : V, (T.card : ℝ) / (Fintype.card V : ℝ) * (indicator S x * adjacencyMatrix G x y)) =
        ((T.card : ℝ) / (Fintype.card V : ℝ) * indicator S x) * (∑ y : V, adjacencyMatrix G x y) := by
      intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    simp_rw [h1, sum_adj_row_eq_degree G hreg]
    have h2 : (∑ x : V, (T.card : ℝ) / (Fintype.card V : ℝ) * indicator S x * (d : ℝ)) =
        ((T.card : ℝ) / (Fintype.card V : ℝ) * (d : ℝ)) * (∑ x : V, indicator S x) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    rw [h2, sum_indicator_univ S]; ring
  have h_T3 : (∑ x : V, ∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * (adjacencyMatrix G x y * indicator T y)) =
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    rw [Finset.sum_comm]
    have h1 : ∀ y : V, (∑ x : V, (S.card : ℝ) / (Fintype.card V : ℝ) * (adjacencyMatrix G x y * indicator T y)) =
        ((S.card : ℝ) / (Fintype.card V : ℝ) * indicator T y) * (∑ x : V, adjacencyMatrix G x y) := by
      intro y; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    simp_rw [h1, sum_adj_col_eq_degree G hreg]
    have h2 : (∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * indicator T y * (d : ℝ)) =
        ((S.card : ℝ) / (Fintype.card V : ℝ) * (d : ℝ)) * (∑ y : V, indicator T y) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    rw [h2, sum_indicator_univ T]; ring
  have h_T4 : (∑ x : V, ∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ)) * adjacencyMatrix G x y) =
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    have h1 : (∑ x : V, ∑ y : V, (S.card : ℝ) / (Fintype.card V : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ)) * adjacencyMatrix G x y) =
        ((S.card : ℝ) / (Fintype.card V : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ))) * (∑ x : V, ∑ y : V, adjacencyMatrix G x y) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]
    have h2 : ((S.card : ℝ) / (Fintype.card V : ℝ) * ((T.card : ℝ) / (Fintype.card V : ℝ))) * ((d : ℝ) * (Fintype.card V : ℝ)) =
        ((d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)) * ((Fintype.card V : ℝ) / (Fintype.card V : ℝ)) := by ring
    rw [h1, sum_adj_all_eq G hreg, h2, div_self hnc, mul_one]
  rw [h_T1, h_T2, h_T3, h_T4]
  ring

/-- Squared norm is the sum of component squares. -/
theorem normSq_eq_sum_sq (v : V → ℝ) : normSq v = ∑ u : V, (v u) ^ 2 := by
  simp only [normSq, innerProduct, sq]

/-- Squared norm is non-negative. -/
theorem normSq_nonneg (v : V → ℝ) : 0 ≤ normSq v := by
  rw [normSq_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Squared norm is zero if and only if the vector is zero. -/
theorem normSq_eq_zero_iff (v : V → ℝ) : normSq v = 0 ↔ v = 0 := by
  simp [normSq_eq_sum_sq, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _), funext_iff]

/-- Squared norm is strictly positive for any non-zero vector. -/
theorem normSq_pos_of_ne_zero {v : V → ℝ} (hne : v ≠ 0) : 0 < normSq v :=
  lt_of_le_of_ne (normSq_nonneg v) (Ne.symm (mt (normSq_eq_zero_iff v).mp hne))

/-- Bilinear Cauchy-Schwarz bound for the adjacency operator:
$\langle u, A v \rangle^2 \le d^2 \|u\|^2 \|v\|^2$. -/
theorem innerProduct_adjOp_sq_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (u v : V → ℝ) :
    (innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)) ^ 2 ≤ (d : ℝ) ^ 2 * normSq u * normSq v := by
  dsimp [innerProduct]
  have h_inner_sq : ∀ x y : V, (adjacencyMatrix G x y * u x) * (adjacencyMatrix G x y * v y) =
      u x * (adjacencyMatrix G x y * v y) := fun x y => by
    dsimp [adjacencyMatrix]; split_ifs <;> ring
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
  rw [h_left, h_right, ← normSq_eq_sum_sq, ← normSq_eq_sum_sq] at h_cs
  calc (∑ p : V × V, (adjacencyMatrix G p.1 p.2 * u p.1) * (adjacencyMatrix G p.1 p.2 * v p.2)) ^ 2
    _ ≤ ((d : ℝ) * normSq u) * ((d : ℝ) * normSq v) := h_cs
    _ = (d : ℝ) ^ 2 * normSq u * normSq v := by ring

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
  rw [← sq_abs (innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y))] at h_sq
  have h_rhs : (d : ℝ) ^ 2 * normSq u * normSq v = ((d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hu_pos.le, Real.sq_sqrt hv_pos.le]; ring
  rw [h_rhs] at h_sq
  have h_nonneg : 0 ≤ (d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by positivity
  have h_le : |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| ≤ (d : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by
    have := sq_le_sq.mp h_sq
    rwa [abs_abs, abs_of_nonneg h_nonneg] at this
  exact (div_le_iff₀ h_denom_pos).mpr h_le

/-- The spectral expansion parameter $\lambda(G) = \max_{i \ge 2} |\lambda_i|$ of a regular graph $G$,
defined variationally as the operator norm of $A$ restricted to $\mathbf{1}^\perp$. -/
noncomputable def spectralExpansionParameter (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }

/-- The spectral expansion parameter is non-negative. -/
theorem spectralExpansionParameter_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ spectralExpansionParameter G := by
  dsimp [spectralExpansionParameter]
  by_cases h_bdd : BddAbove { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }
  · by_cases h_ne : { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }.Nonempty
    · obtain ⟨x, u, v, hu, hv, hu_orth, hv_orth, rfl⟩ := h_ne
      exact le_trans (by positivity) (le_csSup h_bdd ⟨u, v, hu, hv, hu_orth, hv_orth, rfl⟩)
    · rw [Set.not_nonempty_iff_eq_empty.mp h_ne, Real.sSup_empty]
  · rw [Real.sSup_of_not_bddAbove h_bdd]

/--
**The Expander Mixing Lemma (Alon–Chung Bound)**:
For any $d$-regular graph $G = (V, E)$ on $n$ vertices and any subsets $S, T \subseteq V$,
the number of edges $e(S, T)$ between $S$ and $T$ satisfies:
$$\left| e(S, T) - \frac{d |S| |T|}{n} \right| \le \lambda(G) \sqrt{|S| \left(1 - \frac{|S|}{n}\right) |T| \left(1 - \frac{|T|}{n}\right)}$$
-/
theorem expander_mixing_lemma (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S T : Finset V) :
    |edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| ≤
      spectralExpansionParameter G *
        Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
                   (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) := by
  set u := decompPerp S
  set v := decompPerp T
  have hu_norm : normSq u = (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := decompPerp_normSq S hn
  have hv_norm : normSq v = (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) := decompPerp_normSq T hn
  have h_inner : innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y) =
      edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) :=
    innerProduct_decompPerp_eq_edgeCountBetween_sub G hreg hn S T
  by_cases hu : u = 0
  · have : normSq u = 0 := by rw [hu]; simp [normSq, innerProduct]
    have h_prod : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) = 0 := by rwa [← hu_norm]
    have h_lhs : |edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| = 0 := by
      rw [← h_inner, hu]; simp [innerProduct]
    rw [h_lhs, h_prod, zero_mul, zero_mul, Real.sqrt_zero, mul_zero]
  by_cases hv : v = 0
  · have : normSq v = 0 := by rw [hv]; simp [normSq, innerProduct]
    have h_prod : (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) = 0 := by rwa [← hv_norm]
    have h_lhs : |edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| = 0 := by
      rw [← h_inner, hv]; simp [innerProduct]
    have : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) * (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) =
           (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) * ((T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) := by ring
    rw [h_lhs, this, h_prod, mul_zero, Real.sqrt_zero, mul_zero]
  have hu_pos : 0 < normSq u := normSq_pos_of_ne_zero hu
  have hv_pos : 0 < normSq v := normSq_pos_of_ne_zero hv
  have h_denom_pos : 0 < Real.sqrt (normSq u) * Real.sqrt (normSq v) :=
    mul_pos (Real.sqrt_pos.mpr hu_pos) (Real.sqrt_pos.mpr hv_pos)
  have h_elem : |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) ∈
         { |innerProduct u' (fun x => ∑ y : V, adjacencyMatrix G x y * v' y)| /
           (Real.sqrt (normSq u') * Real.sqrt (normSq v')) |
           (u' : V → ℝ) (v' : V → ℝ) (_ : u' ≠ 0) (_ : v' ≠ 0)
           (_ : isOrthogonalToOnes u') (_ : isOrthogonalToOnes v') } :=
    ⟨u, v, hu, hv, decompPerp_orthogonal S hn, decompPerp_orthogonal T hn, rfl⟩
  have h_le := le_csSup (bddAbove_spectralExpansionParameter_set G hreg) h_elem
  have h_mul_le := (div_le_iff₀ h_denom_pos).mp h_le
  rw [h_inner, hu_norm, hv_norm] at h_mul_le
  have h_sqrt_mul : Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) *
         Real.sqrt ((T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) =
         Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
                    (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) := by
    have h1 : 0 ≤ (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by rw [← hu_norm]; positivity
    have h2 : 0 ≤ (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) := by rw [← hv_norm]; positivity
    have : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) * ((T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) =
           (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) * (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) := by ring
    rw [← Real.sqrt_mul h1, this]
  rwa [h_sqrt_mul] at h_mul_le

/-- Bounding the normalized product in the Expander Mixing Lemma by $\sqrt{|S| |T|}$. -/
theorem sqrt_card_sub_le (S T : Finset V) (hn : Fintype.card V ≠ 0) :
    Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
               (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) ≤
    Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hs_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ S)
  have ht_le : (T.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ T)
  have hs1 : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) ≤ (S.card : ℝ) := by
    nlinarith [div_nonneg (Nat.cast_nonneg S.card) (le_of_lt hn_pos)]
  have ht1 : (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) ≤ (T.card : ℝ) := by
    nlinarith [div_nonneg (Nat.cast_nonneg T.card) (le_of_lt hn_pos)]
  have ht1_nonneg : 0 ≤ (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) := by
    have : 0 ≤ 1 - (T.card : ℝ) / (Fintype.card V : ℝ) := by nlinarith [(div_le_one hn_pos).mpr ht_le]
    positivity
  have h_prod : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
                (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) ≤
                (S.card : ℝ) * (T.card : ℝ) := by
    have : (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) * (T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ)) =
           ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) * ((T.card : ℝ) * (1 - (T.card : ℝ) / (Fintype.card V : ℝ))) := by ring
    rw [this]
    exact mul_le_mul hs1 ht1 ht1_nonneg (by positivity)
  exact Real.sqrt_le_sqrt h_prod

/--
**Expander Mixing Lemma (Simplified Form)**:
For any subsets $S, T \subseteq V$ in a $d$-regular graph:
$$\left| e(S, T) - \frac{d |S| |T|}{n} \right| \le \lambda(G) \sqrt{|S| |T|}$$
-/
theorem expander_mixing_lemma_simplified (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (S T : Finset V) :
    |edgeCountBetween G S T - (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| ≤
      spectralExpansionParameter G * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) :=
  (expander_mixing_lemma G hreg hn S T).trans
    (mul_le_mul_of_nonneg_left (sqrt_card_sub_le S T hn) (spectralExpansionParameter_nonneg G))

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
  have hs_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ S)
  have h_em := expander_mixing_lemma G hreg hn S S
  rw [hindep] at h_em
  have h_abs : |0 - (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ)| =
      (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by
    have : 0 ≤ (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by positivity
    rw [show 0 - (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) =
        - ((d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ)) by ring, abs_neg, abs_of_nonneg this]
  have h_sqrt_nonneg : 0 ≤ (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
    have : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ 1 := (div_le_one hn_pos).mpr hs_le
    nlinarith
  have h_sqrt : Real.sqrt ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
                   (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) =
                 (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
    rw [show (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) *
             (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) =
             ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) ^ 2 by ring, Real.sqrt_sq h_sqrt_nonneg]
  rw [h_abs, h_sqrt] at h_em
  by_cases hs : (S.card : ℝ) = 0
  · rw [hs]; positivity
  have hs_pos : 0 < (S.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hs)
  have h_quad : ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) ≤
      spectralExpansionParameter G * (S.card : ℝ) := by
    calc ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ)
      _ = (d : ℝ) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) +
          spectralExpansionParameter G * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by ring
      _ ≤ spectralExpansionParameter G * ((S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ))) +
          spectralExpansionParameter G * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by linarith
      _ = spectralExpansionParameter G * (S.card : ℝ) := by ring
  have h_div : ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) ≤ spectralExpansionParameter G * (Fintype.card V : ℝ) := by
    have : (((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) / (Fintype.card V : ℝ)) * (S.card : ℝ) ≤
        spectralExpansionParameter G * (S.card : ℝ) := by
      calc (((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) / (Fintype.card V : ℝ)) * (S.card : ℝ)
        _ = ((d : ℝ) + spectralExpansionParameter G) * (S.card : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by ring
        _ ≤ spectralExpansionParameter G * (S.card : ℝ) := h_quad
    have h1 := (mul_le_mul_iff_of_pos_right hs_pos).mp this
    exact (div_le_iff₀ hn_pos).mp h1
  have h_denom_pos : 0 < (d : ℝ) + spectralExpansionParameter G := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h_denom_pos]
  linarith

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
  have h_sum_le : (Fintype.card V : ℝ) ≤
      (χ : ℝ) * ((spectralExpansionParameter G / (d + spectralExpansionParameter G)) * (Fintype.card V : ℝ)) := by
    calc (Fintype.card V : ℝ)
      _ = ∑ i : Fin χ, ((Finset.filter (fun v => c v = i) Finset.univ).card : ℝ) := h_fiber
      _ ≤ ∑ i : Fin χ, (spectralExpansionParameter G / (d + spectralExpansionParameter G)) * (Fintype.card V : ℝ) :=
        Finset.sum_le_sum (fun i _ => h_bound_i i)
      _ = (χ : ℝ) * ((spectralExpansionParameter G / (d + spectralExpansionParameter G)) * (Fintype.card V : ℝ)) := by
        simp [nsmul_eq_mul]
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
      have : (spectralExpansionParameter G / ((d : ℝ) + spectralExpansionParameter G)) *
          (((d : ℝ) + spectralExpansionParameter G) / spectralExpansionParameter G) = 1 := by
        rw [div_mul_div_comm, mul_comm (spectralExpansionParameter G) _, div_self (mul_ne_zero hd_ne hl_ne)]
      rw [mul_assoc, this, mul_one]
    rw [h_cancel] at h_step
    linarith
  have h_split : ((d : ℝ) + spectralExpansionParameter G) / spectralExpansionParameter G =
      1 + (d : ℝ) / spectralExpansionParameter G := by
    have hl_ne : spectralExpansionParameter G ≠ 0 := ne_of_gt hpos
    rw [add_div, div_self hl_ne, add_comm]
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
  have h_sqrt_le : Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) ≤ (Fintype.card V : ℝ) := by
    have : (S.card : ℝ) * (T.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
      have : (S.card : ℝ) * (T.card : ℝ) ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) :=
        mul_le_mul hs_le ht_le (Nat.cast_nonneg _) (le_of_lt hn_pos)
      nlinarith
    calc Real.sqrt ((S.card : ℝ) * (T.card : ℝ))
      _ ≤ Real.sqrt ((Fintype.card V : ℝ) ^ 2) := Real.sqrt_le_sqrt this
      _ = (Fintype.card V : ℝ) := Real.sqrt_sq (le_of_lt hn_pos)
  have h_lam_sqrt_le : spectralExpansionParameter G * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) ≤
      spectralExpansionParameter G * (Fintype.card V : ℝ) :=
    mul_le_mul_of_nonneg_left h_sqrt_le (spectralExpansionParameter_nonneg G)
  have h_main_lt : spectralExpansionParameter G * (Fintype.card V : ℝ) <
      (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) := by
    have h1 : spectralExpansionParameter G * (Fintype.card V : ℝ) ^ 2 <
        (S.card : ℝ) * (T.card : ℝ) * (d : ℝ) := (div_lt_iff₀ hd_pos).mp h_size
    have h2 : spectralExpansionParameter G * (Fintype.card V : ℝ) ^ 2 =
        (spectralExpansionParameter G * (Fintype.card V : ℝ)) * (Fintype.card V : ℝ) := by ring
    have h3 : (S.card : ℝ) * (T.card : ℝ) * (d : ℝ) =
        ((d : ℝ) * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)) * (Fintype.card V : ℝ) := by
      have : (S.card : ℝ) * (T.card : ℝ) * (d : ℝ) = (d : ℝ) * (S.card : ℝ) * (T.card : ℝ) := by ring
      rw [this, div_mul_cancel₀ _ (ne_of_gt hn_pos)]
    rw [h2, h3] at h1
    exact (mul_lt_mul_iff_of_pos_right hn_pos).mp h1
  have ⟨h_low, _⟩ := abs_le.mp (expander_mixing_lemma_simplified G hreg hn S T)
  linarith

end ExpanderMixing
