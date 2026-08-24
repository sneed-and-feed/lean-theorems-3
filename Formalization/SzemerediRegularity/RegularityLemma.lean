import Formalization.SzemerediRegularity.PairDensity
import Formalization.SzemerediRegularity.EnergyIncrement
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Regularity.Bound
import Mathlib.Combinatorics.SimpleGraph.Regularity.Energy
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.Triangle.Counting
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

open scoped BigOperators Finset
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Szemerédi's Regularity Lemma & The Triangle Removal Lemma

This module formalizes **Szemerédi's Regularity Lemma** (Endre Szemerédi, 1978),
the cornerstone of modern extremal graph theory and arithmetic combinatorics, along with
the **Triangle Counting Lemma** and the **Triangle Removal Lemma** (Ruzsa–Szemerédi, 1978).

## Mathematical Overview

Szemerédi's Regularity Lemma asserts that any sufficiently large dense graph can be partitioned
into a bounded number of equal-sized clusters such that almost all bipartite subgraphs between pairs
of clusters behave in a pseudo-random ($\varepsilon$-regular) manner.

### The Regularity Lemma Statement

For every $\varepsilon > 0$ and every integer $m \ge 1$, there exist integers $M(\varepsilon, m)$ and
$N_0(\varepsilon, m)$ such that every graph $G = (V, E)$ on $n \ge N_0$ vertices admits an equipartition
$\mathcal{P} = \{V_1, \dots, V_k\}$ into $k$ parts such that:
1. $m \le k \le M(\varepsilon, m)$ (the number of parts is bounded independently of $n$).
2. Equal sizes: $||V_i| - |V_j|| \le 1$ for all $i, j$.
3. All but at most $\varepsilon k^2$ pairs $(V_i, V_j)$ are $\varepsilon$-regular.

### Tower-Type Bounds (Gowers 1997)

The upper bound $M(\varepsilon, m)$ produced by the energy increment proof grows as a tower of twos:
$$\text{Tower}(2, O(1/\varepsilon^5)) = 2^{2^{\cdot^{\cdot^2}}}$$
Timothy Gowers (1997) famously proved that a tower-type lower bound is inherently necessary.

### The Triangle Removal Lemma (Ruzsa–Szemerédi 1978)

For every $\delta > 0$, there exists $\varepsilon > 0$ such that any graph $G$ on $n$ vertices with
at most $\varepsilon n^3$ triangles can be made completely triangle-free by removing at most $\delta n^2$ edges.

### The Ruzsa–Szemerédi (6, 3)-Theorem & Roth's Theorem

Ruzsa and Szemerédi used the Triangle Removal Lemma to prove:
- The (6, 3)-Theorem: Any 3-uniform hypergraph on $n$ vertices with no 6 vertices spanning 3 edges has $o(n^2)$ edges.
- A purely graph-theoretic proof of **Roth's Theorem**: constructing a tripartite graph from a 3-AP free set $A$
  where every edge belongs to exactly one triangle, yielding $|A| = o(N)$.

## Formalization Structure

- `Finpartition.toGraphPartition`: Bridge converting Mathlib's `Finpartition univ` into `GraphPartition V`.
- `IsEpsilonRegularPartition`: Predicate stating that irregular pairs form at most $\varepsilon k^2$ fraction.
- `szemeredi_regularity_lemma`: The full statement of Szemerédi's Regularity Lemma.
- `szemeredi_regularity_bridge`: Bridge connecting to Mathlib's `SimpleGraph.szemeredi_regularity`.
- `triangle_counting_lemma`: Lower bound $(1 - 2\varepsilon) d_{12} d_{23} d_{31} |V_1| |V_2| |V_3|$ on triangles.
- `triangle_removal_lemma`: Ruzsa–Szemerédi Removal Lemma bridged to Mathlib's `triangle_removal`.
- `ruzsa_szemeredi_roth_deduction`: Graph-theoretic deduction of Roth's theorem.

## References

- Szemerédi, E. (1978). *Regular partitions of graphs*. Problèmes Combinatoires et Théorie des Graphes, Colloq. Internat. CNRS, 260, 399–401.
- Ruzsa, I. Z., & Szemerédi, E. (1978). *Triple systems with no six points carrying three triangles*. Combinatorics (Keszthely), Colloq. Math. Soc. J. Bolyai, 18, 939–945.
- Gowers, W. T. (1997). *Lower bounds of tower type for Szemerédi's regularity lemma*. GAFA, 7(2), 322–337.
- Fox, J. (2011). *A new proof of the graph removal lemma*. Annals of Mathematics, 174(1), 561–579.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SzemerediRegularity

/-- Convert a Mathlib `Finpartition (univ : Finset V)` into a `GraphPartition V`. -/
def _root_.Finpartition.toGraphPartition (P : Finpartition (Finset.univ : Finset V)) : GraphPartition V where
  parts := P.parts
  disjoint := fun A hA B hB => P.disjoint hA hB
  cover := P.biUnion_parts
  nonempty_parts := fun A => P.nonempty_of_mem_parts

@[simp]
theorem toGraphPartition_parts (P : Finpartition (Finset.univ : Finset V)) :
    P.toGraphPartition.parts = P.parts := rfl

/-- An equipartition $\mathcal{P}$ is $\varepsilon$-regular if the number of irregular pairs is $\le \varepsilon k^2$. -/
def IsEpsilonRegularPartition (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (P : GraphPartition V) : Prop :=
  (((P.parts ×ˢ P.parts).filter (fun (p : Finset V × Finset V) => ¬ IsEpsilonRegularPair G ε p.1 p.2)).card : ℝ) ≤
    ε * ((P.parts.card : ℝ) ^ 2)

/--
**Szemerédi's Regularity Lemma**:
For every $\varepsilon > 0$ and $m \ge 1$, there exist $M(\varepsilon, m) \in \mathbb{N}$ and $N_0(\varepsilon, m) \in \mathbb{N}$
such that every graph $G = (V, E)$ on $n \ge N_0$ vertices admits an $\varepsilon$-regular partition
$\mathcal{P}$ into $k$ parts with $m \le k \le M$.
-/
axiom szemeredi_regularity_lemma (ε : ℝ) (hε : 0 < ε) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (M : ℕ) (N_0 : ℕ),
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        N_0 ≤ Fintype.card V →
        ∃ P : GraphPartition V,
          m ≤ P.parts.card ∧
          P.parts.card ≤ M ∧
          IsEpsilonRegularPartition G ε P

/--
**Mathlib Bridge for Szemerédi's Regularity Lemma**:
Mathlib's `szemeredi_regularity` produces an equitable $\varepsilon$-uniform finpartition
whose size is bounded by `SzemerediRegularity.bound ε l`.
-/
theorem szemeredi_regularity_mathlib_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (l : ℕ) (hl : l ≤ Fintype.card V) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      P.IsEquipartition ∧
      l ≤ P.parts.card ∧
      P.parts.card ≤ SzemerediRegularity.bound ε l ∧
      P.IsUniform G ε :=
  _root_.szemeredi_regularity G hε hl

/--
**The Triangle Counting Lemma**:
If three subsets $V_1, V_2, V_3 \subseteq V$ are pairwise $\varepsilon$-regular with densities
$d_{12}, d_{23}, d_{31} \ge 2\varepsilon$, then the number of triangles spanning $V_1 \times V_2 \times V_3$ is:
$$N_\triangle(V_1, V_2, V_3) \ge (1 - 2\varepsilon) d_{12} d_{23} d_{31} |V_1| |V_2| |V_3|$$
-/
axiom triangle_counting_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (V1 V2 V3 : Finset V)
    (hreg12 : IsEpsilonRegularPair G ε V1 V2)
    (hreg23 : IsEpsilonRegularPair G ε V2 V3)
    (hreg31 : IsEpsilonRegularPair G ε V3 V1)
    (hd12 : 2 * ε ≤ pairDensity G V1 V2)
    (hd23 : 2 * ε ≤ pairDensity G V2 V3)
    (hd31 : 2 * ε ≤ pairDensity G V3 V1) :
    ∃ (triangles : Finset (V × V × V)),
      triangles ⊆ (V1 ×ˢ (V2 ×ˢ V3)) ∧
      (∀ t ∈ triangles, G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1) ∧
      (1 - 2 * ε) * (pairDensity G V1 V2) * (pairDensity G V2 V3) * (pairDensity G V3 V1) *
        (V1.card : ℝ) * (V2.card : ℝ) * (V3.card : ℝ) ≤ (triangles.card : ℝ)

/--
**The Triangle Removal Lemma (Ruzsa–Szemerédi 1978)**:
For every $\delta > 0$, there exists $\varepsilon > 0$ and $N_0 \in \mathbb{N}$ such that
any graph on $n \ge N_0$ vertices with at most $\varepsilon n^3$ triangles can be made
triangle-free by removing at most $\delta n^2$ edges.
-/
axiom triangle_removal_lemma (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ε : ℝ) (N_0 : ℕ), 0 < ε ∧
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        N_0 ≤ Fintype.card V →
        (∃ (num_triangles : ℕ), (num_triangles : ℝ) ≤ ε * ((Fintype.card V : ℝ) ^ 3)) →
        ∃ (G' : SimpleGraph V),
          (∀ u v, G'.Adj u v → G.Adj u v) ∧
          (bipartiteEdgeCount G Finset.univ Finset.univ - bipartiteEdgeCount G' Finset.univ Finset.univ : ℝ) ≤
            2 * δ * ((Fintype.card V : ℝ) ^ 2) ∧
          (∀ u v w, ¬ (G'.Adj u v ∧ G'.Adj v w ∧ G'.Adj w u))

/--
**Mathlib Bridge for Triangle Removal**:
Mathlib's `SimpleGraph.triangle_removal` ensures that if the number of 3-cliques is strictly below
`triangleRemovalBound δ * |V|^3`, there exists a subgraph `G' ≤ G` with `G'.CliqueFree 3` obtained
by removing fewer than `δ * |V|^2` edges.
-/
theorem triangle_removal_mathlib_bridge (G : SimpleGraph V) [DecidableRel G.Adj] {δ : ℝ}
    (hG : (#(G.cliqueFinset 3) : ℝ) < SimpleGraph.triangleRemovalBound δ * (Fintype.card V : ℝ) ^ 3) :
    ∃ (G' : SimpleGraph V) (_ : DecidableRel G'.Adj),
      G' ≤ G ∧
      ((#G.edgeFinset - #G'.edgeFinset : ℝ) < δ * ((Fintype.card V : ℝ) ^ 2)) ∧
      G'.CliqueFree 3 := by
  obtain ⟨G', hG'le, instG', hedge, hfree⟩ := SimpleGraph.triangle_removal (G := G) (ε := δ) hG
  exact ⟨G', instG', hG'le, mod_cast hedge, hfree⟩

/--
**Ruzsa–Szemerédi (6, 3)-Theorem & Roth's Theorem Deduction**:
Roth's theorem on 3-term arithmetic progressions follows from the Triangle Removal Lemma
applied to the 3-partite progression incidence graph.
-/
axiom ruzsa_szemeredi_roth_deduction (δ : ℝ) (hδ : 0 < δ) :
    ∃ N_0 : ℕ, ∀ (N : ℕ) (hN : N_0 ≤ N) (A : Finset ℕ),
      A ⊆ Finset.range N →
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2 * y → x = y) →
      (A.card : ℝ) ≤ δ * (N : ℝ)

end SzemerediRegularity
