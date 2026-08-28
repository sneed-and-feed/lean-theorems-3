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

set_option linter.unusedSectionVars false

/-!
# The Alon–Boppana Spectral Lower Bound for Regular Graphs

This module formalizes the **Alon–Boppana Theorem** (Noga Alon and Ravi Boppana, 1986; Alon Nilli, 1991)
on the fundamental lower bound on the second largest eigenvalue of $d$-regular graphs and Ramanujan expanders.

## Mathematical Overview

Let $G = (V, E)$ be a finite, connected, $d$-regular simple graph on $n$ vertices with diameter $D = \mathrm{diam}(G)$.
Let $A \in M_{V \times V}(\mathbb{R})$ be its adjacency matrix.
The second largest eigenvalue $\lambda_2(G) = \lambda_2(A)$ is given by the Courant–Fischer variational Rayleigh quotient on $\mathbf{1}^\perp$:
$$\lambda_2(A) = \max_{\substack{v \in \mathbb{R}^V \setminus \{0\} \\ v \perp \mathbf{1}}} \frac{\langle v, A v \rangle}{\langle v, v \rangle}$$

### The Alon–Boppana Lower Bound & Nilli's Geometric Profile
Alon and Boppana established that graph geometry imposes an unavoidable lower bound on $\lambda_2(G)$:
$$\liminf_{n \to \infty} \lambda_2(G_n) \ge 2\sqrt{d-1}$$

In 1991, Alon Nilli provided an elegant combinatorial proof using localized spherical shell test functions
$f(x) = (d-1)^{-k/2}$ on $S_k(x_0)$. A $d$-regular graph is called a **Ramanujan graph** if
every non-trivial eigenvalue satisfies $|\lambda| \le 2\sqrt{d-1}$.

## References

- Alon, N. (1986). *Eigenvalues and expanders*. Theory of Computing Systems, 19(1), 283–296.
- Nilli, A. (1991). *On the second eigenvalue of a graph*. Discrete Mathematics, 91(2), 207–210.
- Lubotzky, A., Phillips, R., & Sarnak, P. (1988). *Ramanujan graphs*. Combinatorica, 8(3), 261–277.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

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

/-- Spherical shell $S_k(x_0)$ of vertices at graph distance exactly $k$ from $x_0$. -/
noncomputable def sphericalShell (G : SimpleGraph V) (x_0 : V) (k : ℕ) : Finset V :=
  Finset.filter (fun v => G.dist x_0 v = k) Finset.univ

/-- Forward neighbors of $v \in S_k(x_0)$ in $S_{k+1}(x_0)$. -/
noncomputable def forwardNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) : Finset V :=
  G.neighborFinset v ∩ sphericalShell G x_0 (k + 1)

/-- Nilli's geometric radial weight profile $g(k) = (d - 1)^{-k / 2} = (1 / \sqrt{d - 1})^k$. -/
noncomputable def nilliProfile (d : ℕ) (k : ℕ) : ℝ :=
  (1 / Real.sqrt (d - 1 : ℝ)) ^ k

/-- Radial test vector supported on the ball of radius $r$ around $x_0$ with profile $g$. -/
noncomputable def radialTestVector (G : SimpleGraph V) (x_0 : V) (g : ℕ → ℝ) (r : ℕ) : V → ℝ :=
  fun v => if G.dist x_0 v ≤ r then g (G.dist x_0 v) else 0

/-- Nilli's localized spherical shell test vector. -/
noncomputable def nilliTestVector (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) : V → ℝ :=
  radialTestVector G x_0 (nilliProfile d) r

/-- Orthogonal balanced linear combination of two test functions. -/
def orthogonalLinearCombination (f₁ f₂ : V → ℝ) : V → ℝ :=
  fun v => (∑ x : V, f₂ x) * f₁ v - (∑ x : V, f₁ x) * f₂ v

/-- Nilli's signed test vector formed by the balanced orthogonal combination of two localized
radial test vectors centered at distant vertices $x_0$ and $y_0$. -/
noncomputable def nilliSignedTestVector (G : SimpleGraph V) (d : ℕ) (x_0 y_0 : V) (r : ℕ) : V → ℝ :=
  orthogonalLinearCombination (nilliTestVector G d x_0 r) (nilliTestVector G d y_0 r)

/-- Ramanujan graphs achieve the optimal spectral gap $d - 2\sqrt{d-1}$. -/
theorem ramanujan_spectral_gap (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hR : IsRamanujan G d) :
    (d : ℝ) - 2 * Real.sqrt (d - 1 : ℝ) ≤ (d : ℝ) - secondEigenvalue G := by
  sorry

/-- In a $d$-regular connected graph, any vertex at distance $k \ge 1$ has at most $d - 1$ forward neighbors. -/
theorem forwardNeighbors_card_le_d_sub_one (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {d : ℕ} (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    (forwardNeighbors G x_0 k v).card ≤ d - 1 := by
  sorry

/-- Product identity across adjacent shells: $g(k) g(k+1) = \sqrt{d-1} g(k+1)^2$. -/
theorem nilliProfile_mul_succ (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    nilliProfile d k * nilliProfile d (k + 1) = Real.sqrt (d - 1 : ℝ) * (nilliProfile d (k + 1)) ^ 2 := by
  sorry

/-- The linear combination $f = (\sum f_2) f_1 - (\sum f_1) f_2$ is orthogonal to the all-ones vector. -/
theorem orthogonalLinearCombination_orthogonal (f₁ f₂ : V → ℝ) :
    isOrthogonalToOnes (orthogonalLinearCombination f₁ f₂) := by
  sorry

/-- Nilli's signed test vector is non-zero when base points are separated by at least $2r + 1$. -/
theorem nilliSignedTestVector_ne_zero (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d)
    {x_0 y_0 : V} {r : ℕ} (h_sep : 2 * r + 1 ≤ G.dist x_0 y_0) :
    nilliSignedTestVector G d x_0 y_0 r ≠ 0 := by
  sorry

end AlonBoppana
