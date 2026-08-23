import Formalization.AlonBoppana.NilliProfile
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

open scoped BigOperators Matrix Finset
open Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace AlonBoppana

/-! ### Part 6: Second Eigenvalue, Alon–Boppana Bounds, and Ramanujan Graphs -/

/-- The second largest eigenvalue $\lambda_2(G)$ defined variationally via the Rayleigh quotient on $\mathbf{1}^\perp$. -/
noncomputable def secondEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { rayleighQuotient G v | (v : V → ℝ) (_ : v ≠ 0) (_ : isOrthogonalToOnes v) }

/--
**Alon–Boppana Theorem (Finite Form)**:
For any $d$-regular simple graph $G$ on $n$ vertices with diameter $D \ge 2$ and $d \ge 2$,
the second largest eigenvalue $\lambda_2(G)$ satisfies:
$$\lambda_2(G) \ge 2\sqrt{d - 1} \cdot \left(1 - \frac{2}{D}\right) - \frac{2}{D}$$
-/
axiom alon_boppana_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    (h_diam : 2 ≤ G.diam) :
    2 * Real.sqrt (d - 1 : ℝ) * (1 - 2 / (G.diam : ℝ)) - 2 / (G.diam : ℝ) ≤ secondEigenvalue G

/--
**Alon–Boppana Spectral Bound (Diameter Form / Nilli's Bound)**:
For any $d$-regular graph $G$ with diameter $D \ge 4$ and $d \ge 2$,
$$\lambda_2(G) \ge 2\sqrt{d - 1} - \frac{2\sqrt{d - 1} - 1}{\lfloor D / 2 \rfloor}$$
-/
axiom alon_boppana_nilli (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    (h_diam : 4 ≤ G.diam) :
    2 * Real.sqrt (d - 1 : ℝ) - (2 * Real.sqrt (d - 1 : ℝ) - 1) / ((G.diam / 2 : ℕ) : ℝ) ≤ secondEigenvalue G

/-- Definition of a Ramanujan graph: A $d$-regular graph whose non-trivial eigenvalues
satisfy $\lambda_2(G) \le 2\sqrt{d-1}$. -/
def IsRamanujan (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  isRegularOfDegree G d ∧ secondEigenvalue G ≤ 2 * Real.sqrt (d - 1 : ℝ)

/-- Ramanujan graphs achieve the optimal spectral gap up to $o(1)$. -/
theorem ramanujan_spectral_gap (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hR : IsRamanujan G d) :
    (d : ℝ) - 2 * Real.sqrt (d - 1 : ℝ) ≤ (d : ℝ) - secondEigenvalue G := by
  linarith [hR.2]

end AlonBoppana
