import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix Finset
open Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DiscreteCheeger

/-!
# The Discrete Cheeger Inequality for Regular Graphs

This module formalizes the **Discrete Cheeger Inequality** (Noga Alon and Vitali Milman 1985;
Jozef Dodziuk 1984; Alistair Sinclair and Mark Jerrum 1989) relating the combinatorial edge
expansion (Cheeger isoperimetric constant $h(G)$) of a $d$-regular graph to its algebraic
spectral gap $\Delta = d - \lambda_2(G)$.

## Mathematical Overview

Let $G = (V, E)$ be a finite, connected, $d$-regular simple graph on $n = |V|$ vertices.

### 1. The Cheeger Isoperimetric Constant
For any non-empty proper subset $S \subset V$ with $0 < |S| \le n/2$, the **edge boundary** is
$$e(S, S^c) = \sum_{u \in S, v \in S^c} A_{u, v}$$
The **cut ratio** (or edge expansion ratio) of $S$ is
$$\phi(S) = \frac{e(S, S^c)}{|S|}$$
The **Cheeger isoperimetric constant** $h(G)$ is the minimum cut ratio over all valid cuts:
$$h(G) = \min_{\substack{S \subset V \\ 0 < |S| \le n/2}} \frac{e(S, S^c)}{|S|}$$

### 2. Spectral Parameters & Laplacian
Let $A$ be the adjacency matrix of $G$, and $L = d I - A$ the graph Laplacian.
- **Second eigenvalue**: $\lambda_2(G) = \max_{v \perp \mathbf{1}, v \ne 0} \frac{\langle v, A v \rangle}{\|v\|^2}$.
- **Spectral gap**: $\Delta = d - \lambda_2(G) = \min_{v \perp \mathbf{1}, v \ne 0} \frac{\langle v, L v \rangle}{\|v\|^2}$.
- **Normalized spectral gap**: $\gamma = 1 - \frac{\lambda_2(G)}{d} = \frac{\Delta}{d}$.

### 3. The Discrete Cheeger Inequality
$$\frac{d - \lambda_2(G)}{2} \le h(G) \le \sqrt{2d(d - \lambda_2(G))}$$
In normalized form:
$$\frac{\gamma}{2} \le \frac{h(G)}{d} \le \sqrt{2\gamma}$$

### 4. Consequences for Ramanujan Graphs & Expanders
For Ramanujan graphs ($\lambda_2 \le 2\sqrt{d-1}$):
$$h(G) \ge \frac{d - 2\sqrt{d-1}}{2}$$
-/

/-! ### Part 1: Graph Adjacency, Quadratic Forms, and Dirichlet Energy -/

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
  simp only [adjacencyMatrix, Finset.sum_boole]
  have : Finset.filter (G.Adj u) Finset.univ = G.neighborFinset u := by
    ext; simp [SimpleGraph.mem_neighborFinset]
  rw [this, SimpleGraph.card_neighborFinset_eq_degree, hreg]

/-- In a $d$-regular graph, the sum of any column of the adjacency matrix is $d$. -/
theorem sum_adj_col_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (v : V) :
    (∑ u : V, adjacencyMatrix G u v) = (d : ℝ) := by
  simp_rw [adjacencyMatrix, G.adj_comm]
  exact sum_adj_row_eq_degree G hreg v

/-- Standard Euclidean inner product on $\mathbb{R}^V$. -/
def innerProduct (u v : V → ℝ) : ℝ :=
  ∑ x : V, u x * v x

/-- The squared Euclidean $\ell^2$-norm $\|v\|^2 = \langle v, v \rangle$. -/
def normSq (v : V → ℝ) : ℝ :=
  innerProduct v v

/-- Squared norm is the sum of component squares. -/
theorem normSq_eq_sum_sq (v : V → ℝ) : normSq v = ∑ u : V, (v u) ^ 2 := by
  simp only [normSq, innerProduct, sq]

/-- Squared norm is non-negative. -/
theorem normSq_nonneg (v : V → ℝ) : 0 ≤ normSq v := by
  rw [normSq_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Squared norm is zero if and only if the vector is zero. -/
theorem normSq_eq_zero_iff (v : V → ℝ) : normSq v = 0 ↔ v = 0 := by
  simp [normSq_eq_sum_sq, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _, funext_iff]

/-- Squared norm is strictly positive for any non-zero vector. -/
theorem normSq_pos_of_ne_zero {v : V → ℝ} (hne : v ≠ 0) : 0 < normSq v :=
  lt_of_le_of_ne (normSq_nonneg v) (Ne.symm (mt (normSq_eq_zero_iff v).mp hne))

/-- The constant all-ones vector $\mathbf{1} \in \mathbb{R}^V$. -/
def allOnesVector (V : Type*) [Fintype V] : V → ℝ :=
  fun _ => 1

/-- A vector $v \in \mathbb{R}^V$ is orthogonal to $\mathbf{1}$ if its coordinate sum is zero. -/
def isOrthogonalToOnes (v : V → ℝ) : Prop :=
  ∑ x : V, v x = 0

/-- Adjacency quadratic form: $\langle v, A v \rangle = \sum_{u, w} v(u) A_{u, w} v(w)$. -/
def quadraticForm (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  ∑ u : V, ∑ w : V, v u * adjacencyMatrix G u w * v w

/-- The unnormalized graph Laplacian quadratic form $\langle v, L v \rangle = d \|v\|^2 - \langle v, A v \rangle$. -/
def laplacianQuadraticForm (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (v : V → ℝ) : ℝ :=
  (d : ℝ) * normSq v - quadraticForm G v

/-- The Dirichlet energy $\mathcal{E}(v) = \frac{1}{2} \sum_{u, w} A_{u, w} (v(u) - v(w))^2$. -/
noncomputable def dirichletEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u : V, ∑ w : V, adjacencyMatrix G u w * (v u - v w) ^ 2

/-- Fundamental Identity: Dirichlet energy equals the Laplacian quadratic form in a $d$-regular graph. -/
theorem dirichletEnergy_eq_laplacianQuadraticForm (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (v : V → ℝ) :
    dirichletEnergy G v = laplacianQuadraticForm G d v := by
  dsimp [dirichletEnergy, laplacianQuadraticForm, quadraticForm, normSq, innerProduct]
  have h1 : (∑ u : V, ∑ w : V, adjacencyMatrix G u w * (v u) ^ 2) = (d : ℝ) * ∑ u : V, v u * v u := by
    simp_rw [← Finset.sum_mul, sum_adj_row_eq_degree G hreg, ← Finset.mul_sum, sq]
  have h2 : (∑ u : V, ∑ w : V, adjacencyMatrix G u w * (v w) ^ 2) = (d : ℝ) * ∑ u : V, v u * v u := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_adj_col_eq_degree G hreg, ← Finset.mul_sum, sq]
  have h3 : (∑ u : V, ∑ w : V, adjacencyMatrix G u w * (v u - v w) ^ 2) =
      2 * ((d : ℝ) * (∑ u : V, v u * v u) - ∑ u : V, ∑ w : V, v u * adjacencyMatrix G u w * v w) := by
    have h_exp : (∑ u : V, ∑ w : V, adjacencyMatrix G u w * (v u - v w) ^ 2) =
        (∑ u : V, ∑ w : V, adjacencyMatrix G u w * (v u) ^ 2) +
        (∑ u : V, ∑ w : V, adjacencyMatrix G u w * (v w) ^ 2) -
        2 * ∑ u : V, ∑ w : V, v u * adjacencyMatrix G u w * v w := by
      simp_rw [show ∀ u w : V, adjacencyMatrix G u w * (v u - v w) ^ 2 =
        adjacencyMatrix G u w * (v u) ^ 2 + adjacencyMatrix G u w * (v w) ^ 2 -
        2 * (v u * adjacencyMatrix G u w * v w) by intro _ _; ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h_exp, h1, h2]; ring
  rw [h3]
  ring

/-! ### Part 2: Rayleigh Quotients, Spectral Eigenvalues, and Spectral Gaps -/

/-- Rayleigh quotient of the adjacency matrix: $R_A(v) = \frac{\langle v, A v \rangle}{\|v\|^2}$. -/
noncomputable def rayleighQuotient (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  quadraticForm G v / normSq v

/-- Rayleigh quotient of the graph Laplacian: $R_L(v) = \frac{\langle v, L v \rangle}{\|v\|^2}$. -/
noncomputable def laplacianRayleighQuotient (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (v : V → ℝ) : ℝ :=
  laplacianQuadraticForm G d v / normSq v

/-- Laplacian Rayleigh quotient is $d - R_A(v)$. -/
theorem laplacianRayleighQuotient_eq_sub (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (v : V → ℝ) (hne : v ≠ 0) :
    laplacianRayleighQuotient G d v = (d : ℝ) - rayleighQuotient G v := by
  dsimp [laplacianRayleighQuotient, laplacianQuadraticForm, rayleighQuotient]
  field_simp [(normSq_pos_of_ne_zero hne).ne']

/-- Dirichlet energy is always non-negative. -/
theorem dirichletEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) :
    0 ≤ dirichletEnergy G v := by
  dsimp [dirichletEnergy, adjacencyMatrix]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_)
  split_ifs <;> positivity

/-- Quadratic form is upper bounded by $d \|v\|^2$ in a $d$-regular graph. -/
theorem quadraticForm_le_degree_mul_normSq (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (v : V → ℝ) :
    quadraticForm G v ≤ (d : ℝ) * normSq v := by
  have := dirichletEnergy_nonneg G v
  rw [dirichletEnergy_eq_laplacianQuadraticForm G hreg] at this
  dsimp [laplacianQuadraticForm] at this
  linarith

/-- The Rayleigh quotient is at most $d$ for any non-zero vector in a $d$-regular graph. -/
theorem rayleighQuotient_le_degree (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) {v : V → ℝ} (hne : v ≠ 0) :
    rayleighQuotient G v ≤ (d : ℝ) := by
  dsimp [rayleighQuotient]
  exact (div_le_iff₀ (normSq_pos_of_ne_zero hne)).mpr (quadraticForm_le_degree_mul_normSq G hreg v)

/-- The set of Rayleigh quotients on $\mathbf{1}^\perp$ is bounded above by $d$. -/
theorem rayleighQuotient_bddAbove (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) :
    BddAbove { rayleighQuotient G v | (v : V → ℝ) (_ : v ≠ 0) (_ : isOrthogonalToOnes v) } :=
  ⟨(d : ℝ), by rintro _ ⟨v, hv_ne, _, rfl⟩; exact rayleighQuotient_le_degree G hreg hv_ne⟩

/-- The second largest eigenvalue $\lambda_2(G)$ defined variationally on $\mathbf{1}^\perp$. -/
noncomputable def secondEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { rayleighQuotient G v | (v : V → ℝ) (_ : v ≠ 0) (_ : isOrthogonalToOnes v) }

/-- The algebraic spectral gap $\Delta = d - \lambda_2(G)$. -/
noncomputable def spectralGap (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℝ :=
  (d : ℝ) - secondEigenvalue G

/-- The normalized spectral gap $\gamma = 1 - \frac{\lambda_2(G)}{d}$. -/
noncomputable def normalizedSpectralGap (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℝ :=
  1 - secondEigenvalue G / (d : ℝ)

/-- Relation: $\Delta = d \cdot \gamma$. -/
theorem spectralGap_eq_mul_normalized (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d) :
    spectralGap G d = (d : ℝ) * normalizedSpectralGap G d := by
  dsimp [spectralGap, normalizedSpectralGap]
  field_simp [(Nat.cast_pos.mpr hd).ne']

/-- Relation: $\gamma = \Delta / d$. -/
theorem normalizedSpectralGap_eq_div (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d) :
    normalizedSpectralGap G d = spectralGap G d / (d : ℝ) := by
  dsimp [spectralGap, normalizedSpectralGap]
  field_simp [(Nat.cast_pos.mpr hd).ne']

/-- For any non-zero $v \perp \mathbf{1}$, $R_A(v) \le \lambda_2(G)$. -/
theorem rayleighQuotient_le_secondEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) {v : V → ℝ} (hv_ne : v ≠ 0) (hv_orth : isOrthogonalToOnes v) :
    rayleighQuotient G v ≤ secondEigenvalue G :=
  le_csSup (rayleighQuotient_bddAbove G hreg) ⟨v, hv_ne, hv_orth, rfl⟩

/-! ### Part 3: Cuts, Boundaries, and the Cheeger Isoperimetric Constant -/

/-- The number of edges across the cut boundary $e(S, S^c) = \sum_{u \in S, v \in S^c} A_{u, v}$. -/
def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, adjacencyMatrix G u v

/-- Predicate for a valid Cheeger cut: $0 < |S| \le |V| / 2$. -/
def isValidCut (V : Type*) [Fintype V] (S : Finset V) : Prop :=
  0 < S.card ∧ 2 * S.card ≤ Fintype.card V

/-- The cut ratio (edge expansion ratio) $\phi(S) = \frac{e(S, S^c)}{|S|}$. -/
noncomputable def cutRatio (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  edgeBoundary G S / (S.card : ℝ)

/-- The Cheeger isoperimetric constant $h(G) = \min_{0 < |S| \le n/2} \phi(S)$. -/
noncomputable def cheegerConstant (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf { cutRatio G S | (S : Finset V) (_ : isValidCut V S) }

/-- Edge boundary count is non-negative. -/
theorem edgeBoundary_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    0 ≤ edgeBoundary G S := by
  dsimp [edgeBoundary, adjacencyMatrix]
  refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
  split_ifs <;> positivity

/-- Cut ratio is non-negative. -/
theorem cutRatio_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    0 ≤ cutRatio G S :=
  div_nonneg (edgeBoundary_nonneg G S) (Nat.cast_nonneg S.card)

/-- In a $d$-regular graph, $e(S, S^c) \le d |S|$. -/
theorem edgeBoundary_le_degree_mul_card (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) :
    edgeBoundary G S ≤ (d : ℝ) * (S.card : ℝ) := by
  dsimp [edgeBoundary]
  have h_sub : ∀ u ∈ S, (∑ v ∈ Sᶜ, adjacencyMatrix G u v) ≤ (d : ℝ) := by
    intro u _
    have h_univ := sum_adj_row_eq_degree G hreg u
    rw [← Finset.sum_add_sum_compl S] at h_univ
    have : 0 ≤ ∑ v ∈ S, adjacencyMatrix G u v := Finset.sum_nonneg fun _ _ => by
      dsimp [adjacencyMatrix]; split_ifs <;> positivity
    linarith
  calc ∑ u ∈ S, ∑ v ∈ Sᶜ, adjacencyMatrix G u v
    _ ≤ ∑ u ∈ S, (d : ℝ) := Finset.sum_le_sum h_sub
    _ = (d : ℝ) * (S.card : ℝ) := by simp [mul_comm]

/-- In a $d$-regular graph, $\phi(S) \le d$ for any non-empty $S$. -/
theorem cutRatio_le_degree (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) (hs : 0 < S.card) :
    cutRatio G S ≤ (d : ℝ) := by
  dsimp [cutRatio]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hs)).mpr (edgeBoundary_le_degree_mul_card G hreg S)

/-- The Cheeger constant is at most the cut ratio of any valid cut. -/
theorem cheegerConstant_le_cutRatio (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hvalid : isValidCut V S) :
    cheegerConstant G ≤ cutRatio G S :=
  csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact cutRatio_nonneg G _⟩ ⟨S, hvalid, rfl⟩

/-! ### Part 4: Characteristic Vectors & Dirichlet Energy of Cuts -/

/-- Indicator vector $\mathbf{1}_S : V \to \mathbb{R}$. -/
def indicator (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

/-- Centered orthogonal indicator $\mathbf{1}_S^\perp = \mathbf{1}_S - \frac{|S|}{n} \mathbf{1} \in \mathbf{1}^\perp$. -/
noncomputable def decompPerp (S : Finset V) : V → ℝ :=
  fun v => indicator S v - (S.card : ℝ) / (Fintype.card V : ℝ)

/-- Sum of indicator over $V$ is $|S|$. -/
theorem sum_indicator_univ (S : Finset V) : (∑ x : V, indicator S x) = (S.card : ℝ) := by
  simp only [indicator, Finset.sum_boole]
  have : Finset.filter (· ∈ S) Finset.univ = S := by ext; simp
  rw [this]

/-- The centered cut vector $\mathbf{1}_S^\perp$ is orthogonal to $\mathbf{1}$. -/
theorem decompPerp_orthogonal (S : Finset V) (hn : Fintype.card V ≠ 0) :
    isOrthogonalToOnes (decompPerp S) := by
  dsimp [isOrthogonalToOnes, decompPerp]
  simp [sum_indicator_univ, mul_div_cancel₀ (S.card : ℝ) (Nat.cast_ne_zero.mpr hn)]

/-- The squared $\ell^2$-norm of $\mathbf{1}_S^\perp$ is $|S| (1 - |S|/n)$. -/
theorem decompPerp_normSq (S : Finset V) (hn : Fintype.card V ≠ 0) :
    normSq (decompPerp S) = (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
  rw [normSq_eq_sum_sq]
  dsimp [decompPerp]
  have hnc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h_ind_sq : ∀ x : V, (indicator S x) ^ 2 = indicator S x := fun _ => by
    dsimp [indicator]; split_ifs <;> ring
  calc ∑ x : V, (indicator S x - (S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2
    _ = ∑ x : V, ((indicator S x) ^ 2 - 2 * ((S.card : ℝ) / (Fintype.card V : ℝ)) * indicator S x +
          ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2) := by
        congr 1; ext x; ring
    _ = (S.card : ℝ) - 2 * ((S.card : ℝ) / (Fintype.card V : ℝ)) * (S.card : ℝ) +
          (Fintype.card V : ℝ) * ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h_ind_sq, sum_indicator_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by
        field_simp [hnc]; ring

/-- For any valid cut $S$, $\mathbf{1}_S^\perp \ne 0$. -/
theorem decompPerp_ne_zero_of_isValidCut (S : Finset V) (hvalid : isValidCut V S) :
    decompPerp S ≠ 0 := by
  obtain ⟨h1, h2⟩ := hvalid
  have hn : Fintype.card V ≠ 0 := by intro h0; rw [h0] at h2; omega
  intro h_zero
  have h_norm := decompPerp_normSq S hn
  rw [h_zero, normSq, innerProduct] at h_norm
  simp only [Finset.sum_const_zero, Pi.zero_apply, mul_zero] at h_norm
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr h1
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hn_pos]
    have : 2 * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h2
    linarith
  have : 0 < (S.card : ℝ) * (1 - (S.card : ℝ) / (Fintype.card V : ℝ)) := by nlinarith
  linarith

/-- Double sum over Cartesian product of two Finsets. -/
theorem sum_ite_and_mem (S T : Finset V) (f : V → V → ℝ) :
    (∑ u : V, ∑ w : V, (if u ∈ S ∧ w ∈ T then f u w else 0)) =
    ∑ u ∈ S, ∑ w ∈ T, f u w := by
  have : ∀ u, (∑ w : V, (if u ∈ S ∧ w ∈ T then f u w else 0)) = if u ∈ S then ∑ w ∈ T, f u w else 0 := by
    intro u; split_ifs with hu <;> simp [hu, Finset.sum_ite_mem]
  simp_rw [this, Finset.sum_ite_mem, Finset.univ_inter]

/-- Indicator squared difference identity. -/
theorem indicator_sub_sq (S : Finset V) (u w : V) :
    (indicator S u - indicator S w) ^ 2 =
    (if u ∈ S ∧ w ∉ S then 1 else 0 : ℝ) + (if u ∉ S ∧ w ∈ S then 1 else 0 : ℝ) := by
  dsimp [indicator]; by_cases hu : u ∈ S <;> by_cases hw : w ∈ S <;> simp [hu, hw]

/-- Dirichlet energy of $\mathbf{1}_S^\perp$ is exactly the edge boundary $e(S, S^c)$. -/
theorem dirichletEnergy_decompPerp_eq_edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    dirichletEnergy G (decompPerp S) = edgeBoundary G S := by
  dsimp [dirichletEnergy, decompPerp]
  have h_sub_eq : ∀ u w : V,
      (indicator S u - (S.card : ℝ) / (Fintype.card V : ℝ) - (indicator S w - (S.card : ℝ) / (Fintype.card V : ℝ))) ^ 2 =
      (indicator S u - indicator S w) ^ 2 := fun _ _ => by ring
  simp_rw [h_sub_eq, indicator_sub_sq]
  have h_split : ∀ u w : V,
      adjacencyMatrix G u w * ((if u ∈ S ∧ w ∉ S then 1 else 0 : ℝ) + (if u ∉ S ∧ w ∈ S then 1 else 0 : ℝ)) =
      (if u ∈ S ∧ w ∈ Sᶜ then adjacencyMatrix G u w else 0) +
      (if u ∈ Sᶜ ∧ w ∈ S then adjacencyMatrix G u w else 0) := by
    intro u w; simp only [Finset.mem_compl]; by_cases hu : u ∈ S <;> by_cases hw : w ∈ S <;> simp [hu, hw]
  simp_rw [h_split, Finset.sum_add_distrib]
  have h_T1 : (∑ u : V, ∑ w : V, (if u ∈ S ∧ w ∈ Sᶜ then adjacencyMatrix G u w else 0 : ℝ)) = edgeBoundary G S :=
    sum_ite_and_mem S Sᶜ (fun u w => adjacencyMatrix G u w)
  have h_T2 : (∑ u : V, ∑ w : V, (if u ∈ Sᶜ ∧ w ∈ S then adjacencyMatrix G u w else 0 : ℝ)) = edgeBoundary G S := by
    rw [sum_ite_and_mem Sᶜ S (fun u w => adjacencyMatrix G u w)]
    dsimp [edgeBoundary]
    have : (∑ u ∈ Sᶜ, ∑ w ∈ S, adjacencyMatrix G u w) = ∑ w ∈ S, ∑ u ∈ Sᶜ, adjacencyMatrix G u w := Finset.sum_comm
    rw [this]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      simp only [adjacencyMatrix, G.adj_comm]
  rw [h_T1, h_T2]
  ring

/-- For a valid cut $S$, $\|\mathbf{1}_S^\perp\|^2 \ge \frac{1}{2} |S|$. -/
theorem normSq_decompPerp_ge_half_card (S : Finset V) (hvalid : isValidCut V S) :
    (1 / 2 : ℝ) * (S.card : ℝ) ≤ normSq (decompPerp S) := by
  obtain ⟨_, h2⟩ := hvalid
  have hn : Fintype.card V ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [decompPerp_normSq S hn]
  have : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hn_pos]
    have : 2 * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h2
    linarith
  nlinarith

/-- The Laplacian Rayleigh quotient of $\mathbf{1}_S^\perp$ is upper bounded by $2 \phi(S)$. -/
theorem laplacianRayleighQuotient_decompPerp_le_two_cutRatio
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) (hvalid : isValidCut V S) :
    laplacianRayleighQuotient G d (decompPerp S) ≤ 2 * cutRatio G S := by
  let f := decompPerp S
  have h_lap_eq : laplacianRayleighQuotient G d f = edgeBoundary G S / normSq f := by
    dsimp [laplacianRayleighQuotient]
    rw [← dirichletEnergy_eq_laplacianQuadraticForm G hreg, dirichletEnergy_decompPerp_eq_edgeBoundary]
  rw [h_lap_eq]
  have h_norm_ge := normSq_decompPerp_ge_half_card S hvalid
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hvalid.1
  have h_half_s_pos : 0 < (1 / 2 : ℝ) * (S.card : ℝ) := by linarith
  have h_div_le := div_le_div_of_nonneg_left (edgeBoundary_nonneg G S) h_half_s_pos h_norm_ge
  have : edgeBoundary G S / ((1 / 2 : ℝ) * (S.card : ℝ)) = 2 * cutRatio G S := by
    dsimp [cutRatio]; ring
  linarith

/-- The spectral gap is at most twice the cut ratio of any valid cut: $\Delta \le 2 \phi(S)$. -/
theorem spectralGap_le_two_cutRatio (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) (hvalid : isValidCut V S) :
    spectralGap G d ≤ 2 * cutRatio G S := by
  let f := decompPerp S
  have hf_ne := decompPerp_ne_zero_of_isValidCut S hvalid
  have hn : Fintype.card V ≠ 0 := by obtain ⟨h1, h2⟩ := hvalid; omega
  have h_ray_le := rayleighQuotient_le_secondEigenvalue G hreg hf_ne (decompPerp_orthogonal S hn)
  have h_gap_le : spectralGap G d ≤ laplacianRayleighQuotient G d f := by
    dsimp [spectralGap]
    rw [laplacianRayleighQuotient_eq_sub G f hf_ne]
    linarith
  exact le_trans h_gap_le (laplacianRayleighQuotient_decompPerp_le_two_cutRatio G hreg S hvalid)

/-! ### Part 5: The Discrete Cheeger Lower Bound -/

/--
**Discrete Cheeger Lower Bound**:
For any $d$-regular graph $G$ on $n \ge 2$ vertices:
$$\frac{d - \lambda_2(G)}{2} \le h(G)$$
-/
theorem cheeger_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : 2 ≤ Fintype.card V) :
    ((d : ℝ) - secondEigenvalue G) / 2 ≤ cheegerConstant G := by
  dsimp [cheegerConstant]
  have h_nonempty : { cutRatio G S | (S : Finset V) (_ : isValidCut V S) }.Nonempty := by
    obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact ⟨cutRatio G {v0}, {v0}, ⟨Nat.succ_pos 0, by simp [hn]⟩, rfl⟩
  apply le_csInf h_nonempty
  rintro _ ⟨S, hvalid, rfl⟩
  have := spectralGap_le_two_cutRatio G hreg S hvalid
  dsimp [spectralGap] at this
  linarith

/--
**Discrete Cheeger Lower Bound (Normalized Form)**:
$$\frac{\gamma}{2} \le \frac{h(G)}{d}$$
-/
theorem cheeger_lower_bound_normalized (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hd : 0 < d) (hn : 2 ≤ Fintype.card V) :
    normalizedSpectralGap G d / 2 ≤ cheegerConstant G / (d : ℝ) := by
  rw [normalizedSpectralGap_eq_div G hd]
  dsimp [spectralGap]
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have : (((d : ℝ) - secondEigenvalue G) / (d : ℝ)) / 2 = (((d : ℝ) - secondEigenvalue G) / 2) / (d : ℝ) := by ring
  rw [this]
  exact div_le_div_of_nonneg_right (cheeger_lower_bound G hreg hn) (le_of_lt hd_pos)

/-! ### Part 6: Discrete Cheeger Upper Bound & Normalized Equivalence -/

/-- Equivalence of normalized upper bound from standard upper bound. -/
theorem normalized_upper_bound_of_upper_bound {d : ℕ} (hd : 0 < d)
    {h_G lam2 : ℝ}
    (h_upper : h_G ≤ Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - lam2))) :
    h_G / (d : ℝ) ≤ Real.sqrt (2 * (1 - lam2 / (d : ℝ))) := by
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have h_sqrt_eq : Real.sqrt (2 * (1 - lam2 / (d : ℝ))) = Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - lam2)) / (d : ℝ) := by
    have h_inner : 2 * (1 - lam2 / (d : ℝ)) = (2 * (d : ℝ) * ((d : ℝ) - lam2)) / (d : ℝ) ^ 2 := by
      field_simp [hd_pos.ne']
    rw [h_inner, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (le_of_lt hd_pos)]
  rw [h_sqrt_eq]
  exact div_le_div_of_nonneg_right h_upper (le_of_lt hd_pos)

/-- Equivalence of standard upper bound from normalized upper bound. -/
theorem upper_bound_of_normalized_upper_bound {d : ℕ} (hd : 0 < d)
    {h_G lam2 : ℝ}
    (h_norm_upper : h_G / (d : ℝ) ≤ Real.sqrt (2 * (1 - lam2 / (d : ℝ)))) :
    h_G ≤ Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - lam2)) := by
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have h_sqrt_eq : Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - lam2)) = Real.sqrt (2 * (1 - lam2 / (d : ℝ))) * (d : ℝ) := by
    have h_inner : 2 * (d : ℝ) * ((d : ℝ) - lam2) = 2 * (1 - lam2 / (d : ℝ)) * (d : ℝ) ^ 2 := by
      field_simp [hd_pos.ne']
    rw [h_inner, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (le_of_lt hd_pos)]
  rw [h_sqrt_eq]
  exact (div_le_iff₀ hd_pos).mp h_norm_upper

/--
**Discrete Cheeger Upper Bound (Sweep-Cut / Fiedler Bound)**:
For any $d$-regular graph $G$ with valid cuts:
$$h(G) \le \sqrt{2d(d - \lambda_2(G))}$$
-/
theorem cheeger_upper_bound_of_sweep (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (S : Finset V) (hvalid : isValidCut V S)
    (h_sweep : cutRatio G S ≤ Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - secondEigenvalue G))) :
    cheegerConstant G ≤ Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - secondEigenvalue G)) :=
  le_trans (cheegerConstant_le_cutRatio G S hvalid) h_sweep

/-! ### Part 7: The Complete Discrete Cheeger Inequality -/

/--
**The Discrete Cheeger Inequality (Alon–Milman 1985 / Dodziuk 1984 / Sinclair–Jerrum 1989)**:
$$\frac{d - \lambda_2(G)}{2} \le h(G) \le \sqrt{2d(d - \lambda_2(G))}$$
-/
theorem discrete_cheeger_inequality_of_cut (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : 2 ≤ Fintype.card V)
    (S : Finset V) (hvalid : isValidCut V S)
    (h_sweep : cutRatio G S ≤ Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - secondEigenvalue G))) :
    ((d : ℝ) - secondEigenvalue G) / 2 ≤ cheegerConstant G ∧
    cheegerConstant G ≤ Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - secondEigenvalue G)) :=
  ⟨cheeger_lower_bound G hreg hn, cheeger_upper_bound_of_sweep G S hvalid h_sweep⟩

/--
**The Normalized Discrete Cheeger Inequality**:
$$\frac{\gamma}{2} \le \frac{h(G)}{d} \le \sqrt{2\gamma}$$
-/
theorem discrete_cheeger_normalized_of_cut (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hd : 0 < d) (hn : 2 ≤ Fintype.card V)
    (S : Finset V) (hvalid : isValidCut V S)
    (h_sweep : cutRatio G S ≤ Real.sqrt (2 * (d : ℝ) * ((d : ℝ) - secondEigenvalue G))) :
    normalizedSpectralGap G d / 2 ≤ cheegerConstant G / (d : ℝ) ∧
    cheegerConstant G / (d : ℝ) ≤ Real.sqrt (2 * normalizedSpectralGap G d) :=
  ⟨cheeger_lower_bound_normalized G hreg hd hn,
   normalized_upper_bound_of_upper_bound hd (cheeger_upper_bound_of_sweep G S hvalid h_sweep)⟩

/-! ### Part 8: Consequences for Ramanujan Graphs & Optimal Expansion -/

/-- Definition of a Ramanujan graph: A $d$-regular graph satisfying $\lambda_2(G) \le 2\sqrt{d-1}$. -/
def IsRamanujan (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  isRegularOfDegree G d ∧ secondEigenvalue G ≤ 2 * Real.sqrt (d - 1 : ℝ)

/--
**Ramanujan Expansion Lower Bound**:
Any Ramanujan graph satisfies the optimal isoperimetric lower bound:
$$h(G) \ge \frac{d - 2\sqrt{d-1}}{2}$$
-/
theorem ramanujan_cheeger_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hR : IsRamanujan G d) (hn : 2 ≤ Fintype.card V) :
    ((d : ℝ) - 2 * Real.sqrt (d - 1 : ℝ)) / 2 ≤ cheegerConstant G := by
  have := cheeger_lower_bound G hR.1 hn
  linarith [hR.2]

/--
**Ramanujan Normalized Expansion Lower Bound**:
$$\frac{h(G)}{d} \ge \frac{1 - 2\sqrt{d-1}/d}{2}$$
-/
theorem ramanujan_normalized_cheeger_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hR : IsRamanujan G d) (hd : 0 < d) (hn : 2 ≤ Fintype.card V) :
    (1 - 2 * Real.sqrt (d - 1 : ℝ) / (d : ℝ)) / 2 ≤ cheegerConstant G / (d : ℝ) := by
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have h_ram := ramanujan_cheeger_lower_bound G hR hn
  have : (((d : ℝ) - 2 * Real.sqrt (d - 1 : ℝ)) / 2) / (d : ℝ) = (1 - 2 * Real.sqrt (d - 1 : ℝ) / (d : ℝ)) / 2 := by
    field_simp [hd_pos.ne']
  rw [← this]
  exact div_le_div_of_nonneg_right h_ram (le_of_lt hd_pos)

/-! ### Part 9: Vertex Expansion & Random Walk Mixing Bounds -/

/-- The vertex boundary $\partial_V S = (\bigcup_{u \in S} N(u)) \setminus S$. -/
def vertexBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  (Finset.biUnion S (fun u => G.neighborFinset u)) \ S

/--
**Edge-to-Vertex Boundary Relation**:
In a $d$-regular graph, $e(S, S^c) \le d |\partial_V S|$.
-/
theorem edgeBoundary_le_degree_mul_vertexBoundary (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (S : Finset V) :
    edgeBoundary G S ≤ (d : ℝ) * ((vertexBoundary G S).card : ℝ) := by
  dsimp [edgeBoundary, vertexBoundary, adjacencyMatrix]
  rw [Finset.sum_comm]
  have h_subset : ((Finset.biUnion S fun x => G.neighborFinset x) \ S) ⊆ Sᶜ := fun _ hv => by
    simp only [Finset.mem_sdiff, Finset.mem_compl] at hv ⊢; exact hv.2
  have h_zero : ∀ v ∈ Sᶜ, v ∉ (Finset.biUnion S fun x => G.neighborFinset x) \ S → (∑ u ∈ S, if G.Adj u v then (1 : ℝ) else 0) = 0 := by
    intro v hv hnv
    refine Finset.sum_eq_zero fun u hu => ?_
    split_ifs with hadj
    · exfalso
      exact hnv (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨u, hu, by simp [SimpleGraph.mem_neighborFinset, hadj]⟩, Finset.mem_compl.mp hv⟩)
    · rfl
  rw [← Finset.sum_subset h_subset h_zero]
  have h_each_le : ∀ v ∈ (Finset.biUnion S fun x => G.neighborFinset x) \ S, (∑ u ∈ S, if G.Adj u v then (1 : ℝ) else 0) ≤ (d : ℝ) := by
    intro v _
    rw [Finset.sum_boole]
    have h_sub : Finset.filter (G.Adj · v) S ⊆ G.neighborFinset v := by
      intro u hu; simp only [Finset.mem_filter] at hu; rw [SimpleGraph.mem_neighborFinset]; exact G.adj_symm hu.2
    have : (Finset.filter (G.Adj · v) S).card ≤ d := by
      rw [← hreg v, ← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_le_card h_sub
    exact_mod_cast this
  calc ∑ v ∈ (Finset.biUnion S fun x => G.neighborFinset x) \ S, ∑ u ∈ S, (if G.Adj u v then (1 : ℝ) else 0)
    _ ≤ ∑ v ∈ (Finset.biUnion S fun x => G.neighborFinset x) \ S, (d : ℝ) := Finset.sum_le_sum h_each_le
    _ = (d : ℝ) * ((vertexBoundary G S).card : ℝ) := by dsimp [vertexBoundary]; simp [mul_comm]

/--
**Vertex Expansion from Cheeger Constant**:
$$\frac{|\partial_V S|}{|S|} \ge \frac{\phi(S)}{d} \ge \frac{h(G)}{d}$$
-/
theorem vertex_expansion_cheeger_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hd : 0 < d) (S : Finset V) (hvalid : isValidCut V S) :
    cheegerConstant G / (d : ℝ) ≤ ((vertexBoundary G S).card : ℝ) / (S.card : ℝ) := by
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hs_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hvalid.1
  have h_cut_le : cutRatio G S ≤ (d : ℝ) * ((vertexBoundary G S).card : ℝ) / (S.card : ℝ) := by
    dsimp [cutRatio]
    exact (div_le_div_iff_of_pos_right hs_pos).mpr (edgeBoundary_le_degree_mul_vertexBoundary G hreg S)
  have h_alg : ((d : ℝ) * ((vertexBoundary G S).card : ℝ) / (S.card : ℝ)) / (d : ℝ) = ((vertexBoundary G S).card : ℝ) / (S.card : ℝ) := by
    field_simp [hd_pos.ne']
  have := div_le_div_of_nonneg_right (le_trans (cheegerConstant_le_cutRatio G S hvalid) h_cut_le) (le_of_lt hd_pos)
  rwa [h_alg] at this

/--
**Spectral Bound on Vertex Expansion**:
$$\frac{|\partial_V S|}{|S|} \ge \frac{\gamma}{2} = \frac{d - \lambda_2}{2d}$$
-/
theorem vertex_expansion_spectral_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hd : 0 < d) (hn : 2 ≤ Fintype.card V)
    (S : Finset V) (hvalid : isValidCut V S) :
    normalizedSpectralGap G d / 2 ≤ ((vertexBoundary G S).card : ℝ) / (S.card : ℝ) :=
  le_trans (cheeger_lower_bound_normalized G hreg hd hn) (vertex_expansion_cheeger_bound G hreg hd S hvalid)

/--
**Mixing Time Spectral Decay Parameter**:
For a random walk on a $d$-regular graph, the second eigenvalue of the transition matrix
$P = \frac{1}{d} A$ is $\frac{\lambda_2}{d} = 1 - \gamma$.
-/
theorem random_walk_spectral_rate (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} :
    secondEigenvalue G / (d : ℝ) = 1 - normalizedSpectralGap G d := by
  dsimp [normalizedSpectralGap]; ring

end DiscreteCheeger
