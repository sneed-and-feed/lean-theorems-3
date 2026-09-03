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

2. **Ramanujan Graphs**: For graphs satisfying the optimal Ramanujan bound $\lambda \le 2\sqrt{d-1}$:
   $$|N(S)| \ge \frac{d^2 |S|}{\frac{(d-2)^2}{n} |S| + 4(d-1)}$$

3. **Subsets of Size $\le n/2$**: For any non-empty $S$ with $|S| \le n/2$:
   $$|N(S)| \ge \frac{2 d^2}{d^2 + \lambda^2} |S|$$

## References

- Tanner, R. M. (1984). *Explicit construction of concentrators from generalized $N$-gons*.
  SIAM Journal on Algebraic and Discrete Methods, 5(3), 287–293.
- Alon, N., & Spencer, J. (2016). *The Probabilistic Method* (4th ed.). Wiley.
- Hoory, S., Linial, N., & Wigderson, A. (2006). *Expander graphs and their applications*.
  Bulletin of the American Mathematical Society, 43(4), 439–561.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TannerExpansion

/-- The $0$-$1$ adjacency matrix of a simple graph $G$ over $\mathbb{R}$. -/
def adjacencyMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/-- Predicate stating that a simple graph is $d$-regular. -/
def isRegularOfDegree (G : SimpleGraph V) (d : ℕ) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = d

/-- Standard Euclidean inner product on $\mathbb{R}^V$. -/
def innerProduct (u v : V → ℝ) : ℝ :=
  ∑ x : V, u x * v x

/-- The squared Euclidean norm $\|v\|^2 = \langle v, v \rangle$. -/
def normSq (v : V → ℝ) : ℝ :=
  innerProduct v v

/-- A vector $v \in \mathbb{R}^V$ is orthogonal to $\mathbf{1}$ if its coordinate sum is zero. -/
def isOrthogonalToOnes (v : V → ℝ) : Prop :=
  ∑ x : V, v x = 0

/-- The spectral expansion parameter $\lambda(G) = \max_{i \ge 2} |\lambda_i|$ of a regular graph $G$. -/
noncomputable def spectralExpansionParameter (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { |innerProduct u (fun x => ∑ y : V, adjacencyMatrix G x y * v y)| /
         (Real.sqrt (normSq u) * Real.sqrt (normSq v)) |
         (u : V → ℝ) (v : V → ℝ) (_ : u ≠ 0) (_ : v ≠ 0)
         (_ : isOrthogonalToOnes u) (_ : isOrthogonalToOnes v) }

/-- The open neighborhood of a vertex set $S \subseteq V$: $N(S) = \bigcup_{u \in S} N(u)$. -/
def neighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.biUnion S (fun u => G.neighborFinset u)

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
  sorry

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
  sorry

/--
**Small Set Expansion via Tanner's Bound**:
If $S \subseteq V$ is non-empty with relative volume $|S|/n \le \alpha$ where $0 < \alpha$,
then $|N(S)| \ge \frac{d^2}{\alpha (d^2 - \lambda^2) + \lambda^2} |S|$.
-/
theorem tanner_small_set_expansion (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (hn : Fintype.card V ≠ 0) (hd : 0 < d)
    (S : Finset V) (hS : 0 < S.card) {α : ℝ} (hα : (S.card : ℝ) / (Fintype.card V : ℝ) ≤ α)
    (hα_pos : 0 < α) :
    ((d : ℝ) ^ 2 / (α * ((d : ℝ) ^ 2 - (spectralExpansionParameter G) ^ 2) + (spectralExpansionParameter G) ^ 2)) * (S.card : ℝ) ≤
    ((neighborhood G S).card : ℝ) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end TannerExpansion
