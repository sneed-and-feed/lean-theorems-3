import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators Finset

set_option linter.unusedSectionVars false

/-!
# Pair Edge Density and $\varepsilon$-Regular Pairs

This module formalizes the fundamental local building blocks of **Szemerédi's Regularity Lemma** (Endre Szemerédi, 1978):
bipartite edge counts, pair edge density $d(X, Y)$, and the definition of $\varepsilon$-regular pairs.

## Mathematical Overview

Let $G = (V, E)$ be a finite simple graph.
For any two non-empty disjoint subsets $X, Y \subseteq V$:
1. The **edge count** $e_G(X, Y)$ is the number of pairs $(u, v) \in X \times Y$ with $u \sim v$:
   $$e_G(X, Y) = |\{ (u, v) \in X \times Y : u \sim v \}| = \sum_{u \in X} \sum_{v \in Y} \mathbf{1}_{\{u \sim v\}}$$
2. The **edge density** $d_G(X, Y)$ is the fraction of possible edges present:
   $$d_G(X, Y) = \frac{e_G(X, Y)}{|X| |Y|}$$
   Clearly, $0 \le d_G(X, Y) \le 1$.

### $\varepsilon$-Regular Pairs

A pair of disjoint vertex subsets $(X, Y)$ is **$\varepsilon$-regular** (for a given parameter $\varepsilon > 0$)
if every reasonably large subset pair inherits approximately the same edge density as $(X, Y)$.

Specifically, $(X, Y)$ is $\varepsilon$-regular if for all $A \subseteq X$ with $|A| \ge \varepsilon |X|$
and all $B \subseteq Y$ with $|B| \ge \varepsilon |Y|$:
$$|d_G(A, B) - d_G(X, Y)| \le \varepsilon$$

Informally, an $\varepsilon$-regular pair behaves like a random bipartite graph $G(|X|, |Y|, p)$
with edge probability $p = d(X, Y)$ at all scales larger than $\varepsilon$.

## Formalization Structure

- `bipartiteEdgeCount`: The number of edges $e_G(X, Y)$ between $X$ and $Y$.
- `pairDensity`: The quotient $d(X, Y) = e_G(X, Y) / (|X| |Y|)$.
- `pairDensity_symm`: Proof that $d(X, Y) = d(Y, X)$ from graph symmetry $u \sim v \iff v \sim u$.
- `pairDensity_le_one`: Proof that $d(X, Y) \le 1$ for non-empty sets.
- `pairDensity_nonneg`: Proof that $d(X, Y) \ge 0$.
- `IsEpsilonRegularPair`: The formal predicate for $\varepsilon$-regularity of a pair $(X, Y)$.

## References

- Szemerédi, E. (1978). *Regular partitions of graphs*. Problèmes Combinatoires et Théorie des Graphes, Colloq. Internat. CNRS, 260, 399–401.
- Komlós, J., & Simonovits, M. (1996). *Szemerédi's Regularity Lemma and its applications in graph theory*. Combinatorics, Paul Erdős is Eighty, 2, 295–352.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SzemerediRegularity

/-- The number of edges between two subsets $X, Y \subseteq V$ in a simple graph $G$. -/
def bipartiteEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℕ :=
  ((X ×ˢ Y).filter (fun p => G.Adj p.1 p.2)).card

/-- The edge density $d(X, Y) = \frac{e(X, Y)}{|X| |Y|}$ between non-empty sets $X, Y$. -/
noncomputable def pairDensity (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℝ :=
  (bipartiteEdgeCount G X Y : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))

/-- Symmetry of bipartite edge count: $e(X, Y) = e(Y, X)$. -/
theorem bipartiteEdgeCount_symm (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    bipartiteEdgeCount G X Y = bipartiteEdgeCount G Y X := by
  dsimp [bipartiteEdgeCount]
  rw [← Finset.card_map ⟨Prod.swap, Prod.swap_injective⟩]
  congr 1
  ext ⟨y, x⟩
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_product, Function.Embedding.coeFn_mk,
    Prod.exists, Prod.swap, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hadj⟩, rfl, rfl⟩
    exact ⟨⟨hb, ha⟩, G.adj_symm hadj⟩
  · rintro ⟨⟨hy, hx⟩, hadj⟩
    exact ⟨x, y, ⟨⟨hx, hy⟩, G.adj_symm hadj⟩, rfl, rfl⟩

/-- Symmetry of pair density: $d(X, Y) = d(Y, X)$. -/
theorem pairDensity_symm (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    pairDensity G X Y = pairDensity G Y X := by
  dsimp [pairDensity]
  rw [bipartiteEdgeCount_symm G X Y, mul_comm (X.card : ℝ) (Y.card : ℝ)]

/-- The edge density is bounded in $[0, 1]$ for non-empty sets. -/
theorem pairDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity G X Y ≤ 1 := by
  dsimp [pairDensity]
  have h_le : bipartiteEdgeCount G X Y ≤ X.card * Y.card := by
    dsimp [bipartiteEdgeCount]
    have h_sub : (X ×ˢ Y).filter (fun p => G.Adj p.1 p.2) ⊆ X ×ˢ Y := Finset.filter_subset _ _
    have h_card := Finset.card_le_card h_sub
    rwa [Finset.card_product] at h_card
  have h_pos : 0 < (X.card : ℝ) * (Y.card : ℝ) := by
    have hXpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
    have hYpos : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
    positivity
  rw [div_le_one₀ h_pos, ← Nat.cast_mul]
  exact Nat.cast_le (α := ℝ).2 h_le

/-- The edge density is non-negative. -/
theorem pairDensity_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    0 ≤ pairDensity G X Y := by
  dsimp [pairDensity]
  exact div_nonneg (Nat.cast_nonneg (α := ℝ) (bipartiteEdgeCount G X Y))
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) X.card) (Nat.cast_nonneg (α := ℝ) Y.card))

/--
**Definition of an $\varepsilon$-Regular Pair**:
A disjoint pair $(X, Y)$ is $\varepsilon$-regular if for all $A \subseteq X$ with $|A| \ge \varepsilon |X|$
and all $B \subseteq Y$ with $|B| \ge \varepsilon |Y|$, the sub-pair density satisfies:
$$|d_G(A, B) - d_G(X, Y)| \le \varepsilon$$
-/
def IsEpsilonRegularPair (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (X Y : Finset V) : Prop :=
  ∀ (A : Finset V) (B : Finset V),
    A ⊆ X → B ⊆ Y →
    ε * (X.card : ℝ) ≤ (A.card : ℝ) →
    ε * (Y.card : ℝ) ≤ (B.card : ℝ) →
    |pairDensity G A B - pairDensity G X Y| ≤ ε

end SzemerediRegularity
