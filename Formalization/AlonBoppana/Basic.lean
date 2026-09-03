import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix Finset
open Classical

variable {V : Type*} [Fintype V]

namespace AlonBoppana

/-! ### Part 1: Adjacency Matrix, Quadratic Forms, and Rayleigh Quotients -/

/-- The $0$-$1$ adjacency matrix of a simple graph $G$ over $\mathbb{R}$. -/
def adjacencyMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/-- Predicate stating that a simple graph is $d$-regular. -/
def isRegularOfDegree (G : SimpleGraph V) (d : ℕ) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = d

/-- The all-ones vector $\mathbf{1} \in \mathbb{R}^V$. -/
def allOnesVector (V : Type*) [Fintype V] : V → ℝ :=
  fun _ => 1

/-- Standard Euclidean inner product on $\mathbb{R}^V$. -/
def innerProduct (u v : V → ℝ) : ℝ :=
  ∑ x : V, u x * v x

/-- The squared Euclidean $\ell^2$-norm $\|v\|^2 = \langle v, v \rangle$. -/
def normSq (v : V → ℝ) : ℝ :=
  innerProduct v v

/-- Quadratic form of the adjacency matrix: $\langle v, A v \rangle = \sum_{u, w} v(u) A(u, w) v(w)$. -/
def quadraticForm (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  ∑ u : V, ∑ w : V, v u * adjacencyMatrix G u w * v w

/-- Rayleigh quotient $R(v) = \frac{\langle v, A v \rangle}{\langle v, v \rangle}$ for $v \ne 0$. -/
noncomputable def rayleighQuotient (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  quadraticForm G v / normSq v

/-- A vector $v \in \mathbb{R}^V$ is orthogonal to the all-ones vector $\mathbf{1}$ if $\sum_{x \in V} v(x) = 0$. -/
def isOrthogonalToOnes (v : V → ℝ) : Prop :=
  ∑ x : V, v x = 0

omit [Fintype V] in
/-- Adjacency matrix is symmetric for any simple graph. -/
theorem adjacencyMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyMatrix G)ᵀ = adjacencyMatrix G := by
  ext u v
  simp only [Matrix.transpose_apply, adjacencyMatrix, SimpleGraph.adj_comm G]

/-- For a $d$-regular graph, the all-ones vector satisfies $A \mathbf{1} = d \mathbf{1}$. -/
theorem adjacencyMatrix_mul_ones (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (u : V) :
    (∑ w : V, adjacencyMatrix G u w * allOnesVector V w) = (d : ℝ) := by
  simp only [adjacencyMatrix, allOnesVector, mul_one]
  have h_sum : (∑ w : V, if G.Adj u w then (1 : ℝ) else 0) =
      ((Finset.filter (fun w => G.Adj u w) Finset.univ).card : ℝ) :=
    Finset.sum_boole (fun w => G.Adj u w) Finset.univ
  rw [h_sum]
  have h_card : (Finset.filter (fun w => G.Adj u w) Finset.univ).card = G.degree u := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset]
    congr 1; ext w; simp
  rw [h_card, hreg u]

/-- Squared norm is the sum of component squares. -/
theorem normSq_eq_sum_sq (v : V → ℝ) : normSq v = ∑ u : V, (v u) ^ 2 := by
  simp only [normSq, innerProduct, sq]

/-- Squared norm is non-negative. -/
theorem normSq_nonneg (v : V → ℝ) : 0 ≤ normSq v := by
  rw [normSq_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Squared norm is zero if and only if the vector is zero. -/
theorem normSq_eq_zero_iff (v : V → ℝ) : normSq v = 0 ↔ v = 0 := by
  rw [normSq_eq_sum_sq]
  constructor
  · intro h
    ext x
    have h_nonneg : ∀ y ∈ (Finset.univ : Finset V), 0 ≤ (v y) ^ 2 := fun _ _ => sq_nonneg _
    have h_sq := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h x (Finset.mem_univ x)
    exact sq_eq_zero_iff.mp h_sq
  · rintro rfl; simp

/-- Squared norm is strictly positive for any non-zero vector. -/
theorem normSq_pos_of_ne_zero {v : V → ℝ} (hne : v ≠ 0) : 0 < normSq v :=
  lt_of_le_of_ne (normSq_nonneg v) (Ne.symm (mt (normSq_eq_zero_iff v).mp hne))

/-- Quadratic form written as sum over adjacent pairs. -/
theorem quadraticForm_eq_sum_adj (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) :
    quadraticForm G v = ∑ u : V, ∑ w : V, if G.Adj u w then v u * v w else 0 := by
  simp only [quadraticForm, adjacencyMatrix]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

/-- Quadratic form expressed via neighbor finset summation. -/
theorem quadraticForm_eq_sum_neighbor (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) :
    quadraticForm G v = ∑ u : V, v u * ∑ w ∈ G.neighborFinset u, v w := by
  rw [quadraticForm_eq_sum_adj]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_filter]
  congr 1; ext w
  simp [SimpleGraph.mem_neighborFinset]

end AlonBoppana
