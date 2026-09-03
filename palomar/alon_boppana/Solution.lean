import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix Finset
open Classical


variable {V : Type*} [Fintype V]

namespace AlonBoppana

/-- The $0$-$1$ adjacency matrix of a simple graph $G$ over $\mathbb{R}$. -/
def adjacencyMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/-- Predicate stating that a simple graph is $d$-regular. -/
def isRegularOfDegree (G : SimpleGraph V) (d : ℕ) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = d

/-- Standard Euclidean inner product on $\mathbb{R}^V$. -/
def innerProduct (u v : V → ℝ) : ℝ :=
  ∑ x : V, u x * v x

/-- The squared Euclidean $\ell^2$-norm $\|v\|^2 = \langle v, v \rangle$. -/
def normSq (v : V → ℝ) : ℝ :=
  innerProduct v v

/-- Quadratic form of the adjacency matrix. -/
def quadraticForm (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  ∑ u : V, ∑ w : V, v u * adjacencyMatrix G u w * v w

/-- Rayleigh quotient $R(v) = \frac{\langle v, A v \rangle}{\langle v, v \rangle}$ for $v \ne 0$. -/
noncomputable def rayleighQuotient (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  quadraticForm G v / normSq v

/-- A vector $v \in \mathbb{R}^V$ is orthogonal to the all-ones vector $\mathbf{1}$ if $\sum_{x \in V} v(x) = 0$. -/
def isOrthogonalToOnes (v : V → ℝ) : Prop :=
  ∑ x : V, v x = 0

/-- The second largest eigenvalue $\lambda_2(G)$ defined variationally via the Rayleigh quotient on $\mathbf{1}^\perp$. -/
noncomputable def secondEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { rayleighQuotient G v | (v : V → ℝ) (_ : v ≠ 0) (_ : isOrthogonalToOnes v) }

/-- Definition of a Ramanujan graph: A $d$-regular graph whose second eigenvalue satisfies $\lambda_2(G) \le 2\sqrt{d-1}$. -/
def IsRamanujan (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  isRegularOfDegree G d ∧ secondEigenvalue G ≤ 2 * Real.sqrt (d - 1 : ℝ)

/-- Ramanujan graphs achieve the optimal spectral gap $d - 2\sqrt{d-1}$. -/
theorem ramanujan_spectral_gap (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hR : IsRamanujan G d) :
    (d : ℝ) - 2 * Real.sqrt (d - 1 : ℝ) ≤ (d : ℝ) - secondEigenvalue G := by
  linarith [hR.2]

/-- Spherical shell $S_k(x_0)$ of vertices at graph distance exactly $k$ from $x_0$. -/
noncomputable def sphericalShell (G : SimpleGraph V) (x_0 : V) (k : ℕ) : Finset V :=
  Finset.filter (fun v => G.dist x_0 v = k) Finset.univ

/-- Membership in a spherical shell corresponds to graph distance. -/
theorem sphericalShell_mem_iff (G : SimpleGraph V) (x_0 : V) (k : ℕ) (v : V) :
    v ∈ sphericalShell G x_0 k ↔ G.dist x_0 v = k := by
  simp [sphericalShell]

/-- Spherical shells at distinct distances are disjoint. -/
theorem sphericalShell_disjoint (G : SimpleGraph V) (x_0 : V) {j k : ℕ} (h : j ≠ k) :
    Disjoint (sphericalShell G x_0 j) (sphericalShell G x_0 k) := by
  rw [Finset.disjoint_left]
  intro x hj hk
  rw [sphericalShell_mem_iff] at hj hk
  exact h (hj.symm.trans hk)

/-- Backward neighbors of $v \in S_k(x_0)$ in $S_{k-1}(x_0)$. -/
noncomputable def backwardNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) : Finset V :=
  G.neighborFinset v ∩ sphericalShell G x_0 (k - 1)

/-- Internal neighbors of $v \in S_k(x_0)$ in $S_k(x_0)$. -/
noncomputable def internalNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) : Finset V :=
  G.neighborFinset v ∩ sphericalShell G x_0 k

/-- Forward neighbors of $v \in S_k(x_0)$ in $S_{k+1}(x_0)$. -/
noncomputable def forwardNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) : Finset V :=
  G.neighborFinset v ∩ sphericalShell G x_0 (k + 1)

/-- In a connected graph, every vertex at distance $k \ge 1$ has a neighbor at distance $k - 1$. -/
theorem exists_neighbor_dist_sub_one (G : SimpleGraph V) (x_0 : V) (hconn : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : G.dist x_0 v = k) :
    ∃ w : V, G.Adj v w ∧ G.dist x_0 w = k - 1 := by
  rcases SimpleGraph.Connected.exists_walk_length_eq_dist hconn v x_0 with ⟨p, hp⟩
  have hv' : G.dist v x_0 = k := by rw [SimpleGraph.dist_comm, hv]
  rw [hv'] at hp
  cases p with
  | nil =>
    have : 0 = k := by simpa using hp
    omega
  | cons hadj p' =>
    rename_i w
    have hp' : p'.length = k - 1 := by
      have : p'.length + 1 = k := by simpa [SimpleGraph.Walk.length_cons] using hp
      omega
    have hdist_le : G.dist w x_0 ≤ k - 1 := by
      rw [← hp']; exact G.dist_le p'
    rw [SimpleGraph.dist_comm (u := w) (v := x_0)] at hdist_le
    have h_tri := hadj.diff_dist_adj (u := x_0)
    rw [hv] at h_tri
    have hdist_eq : G.dist x_0 w = k - 1 := by omega
    exact ⟨w, hadj, hdist_eq⟩

/-- Every vertex in $S_k(x_0)$ ($k \ge 1$) has at least 1 backward neighbor in $S_{k-1}(x_0)$. -/
theorem card_backwardNeighbors_ge_one (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    (hconn : G.Connected) {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    1 ≤ (backwardNeighbors G x_0 k v).card := by
  rw [sphericalShell_mem_iff] at hv
  rcases exists_neighbor_dist_sub_one G x_0 hconn hk hv with ⟨w, hadj, hw⟩
  have hw_mem : w ∈ backwardNeighbors G x_0 k v := by
    simp only [backwardNeighbors, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      sphericalShell_mem_iff]
    exact ⟨hadj, hw⟩
  exact Finset.card_pos.mpr ⟨w, hw_mem⟩

/-- All neighbors of $v \in S_k(x_0)$ lie in $S_{k-1} \cup S_k \cup S_{k+1}$. -/
theorem neighbor_subset_shells (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    G.neighborFinset v ⊆ backwardNeighbors G x_0 k v ∪ internalNeighbors G x_0 k v ∪ forwardNeighbors G x_0 k v := by
  intro w hw
  rw [sphericalShell_mem_iff] at hv
  have hadj : G.Adj v w := by simpa [SimpleGraph.mem_neighborFinset] using hw
  have h_tri := hadj.diff_dist_adj (u := x_0)
  rw [hv] at h_tri
  simp only [Finset.mem_union, backwardNeighbors, internalNeighbors, forwardNeighbors,
    Finset.mem_inter, hw, true_and, sphericalShell_mem_iff]
  rcases h_tri with h1 | h2 | h3
  · left; right; exact h1
  · right; exact h2
  · left; left; exact h3

/-- The neighborhood of $v \in S_k(x_0)$ partitions into backward, internal, and forward neighbors. -/
theorem neighborFinset_eq_union (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    G.neighborFinset v = backwardNeighbors G x_0 k v ∪ internalNeighbors G x_0 k v ∪ forwardNeighbors G x_0 k v := by
  apply Finset.Subset.antisymm (neighbor_subset_shells G x_0 hv)
  intro w hw
  simp only [Finset.mem_union, backwardNeighbors, internalNeighbors, forwardNeighbors, Finset.mem_inter] at hw
  rcases hw with (⟨hw1, _⟩ | ⟨hw1, _⟩) | ⟨hw1, _⟩ <;> exact hw1

/-- Backward neighbors and internal neighbors are disjoint for $k \ge 1$. -/
theorem disjoint_backward_internal (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} (hk : 1 ≤ k) (v : V) :
    Disjoint (backwardNeighbors G x_0 k v) (internalNeighbors G x_0 k v) := by
  apply Finset.disjoint_of_subset_right Finset.inter_subset_right
  apply Finset.disjoint_of_subset_left Finset.inter_subset_right
  apply sphericalShell_disjoint; omega

/-- Backward neighbors and forward neighbors are disjoint. -/
theorem disjoint_backward_forward (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) :
    Disjoint (backwardNeighbors G x_0 k v) (forwardNeighbors G x_0 k v) := by
  apply Finset.disjoint_of_subset_right Finset.inter_subset_right
  apply Finset.disjoint_of_subset_left Finset.inter_subset_right
  apply sphericalShell_disjoint; omega

/-- Internal neighbors and forward neighbors are disjoint. -/
theorem disjoint_internal_forward (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) :
    Disjoint (internalNeighbors G x_0 k v) (forwardNeighbors G x_0 k v) := by
  apply Finset.disjoint_of_subset_right Finset.inter_subset_right
  apply Finset.disjoint_of_subset_left Finset.inter_subset_right
  apply sphericalShell_disjoint; omega

/-- Cardinality degree split across backward, internal, and forward neighbor sets. -/
theorem card_neighbors_split (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    (G.neighborFinset v).card =
      (backwardNeighbors G x_0 k v).card + (internalNeighbors G x_0 k v).card + (forwardNeighbors G x_0 k v).card := by
  rw [neighborFinset_eq_union G x_0 hv, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint (disjoint_backward_internal G x_0 hk v)]
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_backward_forward G x_0 k v, disjoint_internal_forward G x_0 k v⟩

/-- In a $d$-regular connected graph, any vertex at distance $k \ge 1$ has at most $d - 1$ forward neighbors. -/
theorem forwardNeighbors_card_le_d_sub_one (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {d : ℕ} (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    (forwardNeighbors G x_0 k v).card ≤ d - 1 := by
  have h_split := card_neighbors_split G x_0 hk hv
  have h_deg : (G.neighborFinset v).card = d := by
    rw [← SimpleGraph.degree, hreg v]
  rw [h_deg] at h_split
  have h_back := card_backwardNeighbors_ge_one G x_0 hconn hk hv
  omega

/-- Nilli's geometric radial weight profile $g(k) = (d - 1)^{-k / 2} = (1 / \sqrt{d - 1})^k$. -/
noncomputable def nilliProfile (d : ℕ) (k : ℕ) : ℝ :=
  (1 / Real.sqrt (d - 1 : ℝ)) ^ k

/-- Step recurrence for Nilli profile: $g(k+1) = g(k) / \sqrt{d-1}$. -/
theorem nilliProfile_succ (d : ℕ) (k : ℕ) :
    nilliProfile d (k + 1) = nilliProfile d k * (1 / Real.sqrt (d - 1 : ℝ)) := by
  unfold nilliProfile
  exact pow_succ (1 / Real.sqrt (d - 1 : ℝ)) k

/-- Product identity across adjacent shells: $g(k) g(k+1) = \sqrt{d-1} g(k+1)^2$. -/
theorem nilliProfile_mul_succ (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    nilliProfile d k * nilliProfile d (k + 1) = Real.sqrt (d - 1 : ℝ) * (nilliProfile d (k + 1)) ^ 2 := by
  have hd_pos : 0 < (d - 1 : ℝ) := by
    have : (d : ℝ) ≥ 2 := Nat.cast_le.mpr hd
    linarith
  have h_sqrt_ne : Real.sqrt (d - 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_pos)
  rw [nilliProfile_succ]
  set s := Real.sqrt (d - 1 : ℝ)
  set g := nilliProfile d k
  have h_cancel : s * (1 / s) = 1 := mul_one_div_cancel h_sqrt_ne
  calc g * (g * (1 / s))
    _ = g ^ 2 * (s * (1 / s) * (1 / s)) := by rw [h_cancel, one_mul]; ring
    _ = s * (g * (1 / s)) ^ 2 := by ring

/-- Radial test vector supported on the ball of radius $r$ around $x_0$ with profile $g$. -/
noncomputable def radialTestVector (G : SimpleGraph V) (x_0 : V) (g : ℕ → ℝ) (r : ℕ) : V → ℝ :=
  fun v => if G.dist x_0 v ≤ r then g (G.dist x_0 v) else 0

/-- Nilli's localized spherical shell test vector. -/
noncomputable def nilliTestVector (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) : V → ℝ :=
  radialTestVector G x_0 (nilliProfile d) r

omit [Fintype V] in
/-- Test vector evaluated at the center vertex $x_0$ equals 1. -/
theorem nilliTestVector_center (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) :
    nilliTestVector G d x_0 r x_0 = 1 := by
  simp [nilliTestVector, radialTestVector, SimpleGraph.dist_self, nilliProfile]

/-- Positivity of the Nilli profile for $d \ge 2$. -/
theorem nilliProfile_pos (d : ℕ) (hd : 2 ≤ d) (k : ℕ) : 0 < nilliProfile d k := by
  have hd_pos : 0 < (d - 1 : ℝ) := by
    have : (d : ℝ) ≥ 2 := Nat.cast_le.mpr hd
    linarith
  exact pow_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hd_pos)) k

/-- Nonnegativity of the Nilli profile for $d \ge 2$. -/
theorem nilliProfile_nonneg (d : ℕ) (hd : 2 ≤ d) (k : ℕ) : 0 ≤ nilliProfile d k :=
  le_of_lt (nilliProfile_pos d hd k)

omit [Fintype V] in
/-- Nilli test vector is point-wise non-negative. -/
theorem nilliTestVector_nonneg (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d) (x_0 : V) (r : ℕ) (v : V) :
    0 ≤ nilliTestVector G d x_0 r v := by
  simp only [nilliTestVector, radialTestVector]
  split_ifs with h
  · exact nilliProfile_nonneg d hd (G.dist x_0 v)
  · rfl

/-- Sum of values of the Nilli test vector is strictly positive. -/
theorem nilliTestVector_sum_pos (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d) (x_0 : V) (r : ℕ) :
    0 < ∑ v : V, nilliTestVector G d x_0 r v := by
  have h_center : 0 < nilliTestVector G d x_0 r x_0 := by
    rw [nilliTestVector_center]
    norm_num
  have h_nonneg : ∀ v ∈ (Finset.univ : Finset V), 0 ≤ nilliTestVector G d x_0 r v :=
    fun v _ => nilliTestVector_nonneg G d hd x_0 r v
  have h_le := Finset.single_le_sum h_nonneg (Finset.mem_univ x_0)
  exact lt_of_lt_of_le h_center h_le

/-- Orthogonal balanced linear combination of two test functions. -/
def orthogonalLinearCombination (f₁ f₂ : V → ℝ) : V → ℝ :=
  fun v => (∑ x : V, f₂ x) * f₁ v - (∑ x : V, f₁ x) * f₂ v

/-- The linear combination $f = (\sum f_2) f_1 - (\sum f_1) f_2$ is orthogonal to the all-ones vector. -/
theorem orthogonalLinearCombination_orthogonal (f₁ f₂ : V → ℝ) :
    isOrthogonalToOnes (orthogonalLinearCombination f₁ f₂) := by
  simp only [isOrthogonalToOnes, orthogonalLinearCombination]
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  ring

/-- Nilli's signed test vector formed by the balanced orthogonal combination of two localized
radial test vectors centered at distant vertices $x_0$ and $y_0$. -/
noncomputable def nilliSignedTestVector (G : SimpleGraph V) (d : ℕ) (x_0 y_0 : V) (r : ℕ) : V → ℝ :=
  orthogonalLinearCombination (nilliTestVector G d x_0 r) (nilliTestVector G d y_0 r)

omit [Fintype V] in
/-- Test vector evaluates to zero outside the support ball. -/
theorem nilliTestVector_apply_of_gt (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) {v : V}
    (h : r < G.dist x_0 v) :
    nilliTestVector G d x_0 r v = 0 := by
  simp [nilliTestVector, radialTestVector, not_le.mpr h]

/-- Nilli's signed test vector is non-zero when the base points are separated by at least $2r + 1$. -/
theorem nilliSignedTestVector_ne_zero (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d)
    {x_0 y_0 : V} {r : ℕ} (h_sep : 2 * r + 1 ≤ G.dist x_0 y_0) :
    nilliSignedTestVector G d x_0 y_0 r ≠ 0 := by
  intro h_zero
  have h_val : nilliSignedTestVector G d x_0 y_0 r x_0 = 0 := by rw [h_zero]; rfl
  simp only [nilliSignedTestVector, orthogonalLinearCombination] at h_val
  have h1 : nilliTestVector G d x_0 r x_0 = 1 := nilliTestVector_center G d x_0 r
  have h2 : nilliTestVector G d y_0 r x_0 = 0 := by
    apply nilliTestVector_apply_of_gt
    rw [SimpleGraph.dist_comm]
    linarith
  rw [h1, h2, mul_one, mul_zero, sub_zero] at h_val
  have h_pos := nilliTestVector_sum_pos G d hd y_0 r
  linarith

end AlonBoppana
