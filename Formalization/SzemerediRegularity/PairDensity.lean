import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

open scoped BigOperators Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Pair Edge Density and $\varepsilon$-Regular Pairs

This module formalizes the fundamental local building blocks of **Szemerédi's Regularity Lemma** (Endre Szemerédi, 1978):
bipartite edge counts, pair edge density $d(X, Y)$, and the definition of $\varepsilon$-regular pairs.

## Mathematical Overview

Let $G = (V, E)$ be a finite simple graph.
For any two subsets $X, Y \subseteq V$:
1. The **edge count** $e_G(X, Y)$ is the number of pairs $(u, v) \in X \times Y$ with $u \sim v$:
   $$e_G(X, Y) = |\{ (u, v) \in X \times Y : u \sim v \}| = \sum_{u \in X} \sum_{v \in Y} \mathbf{1}_{\{u \sim v\}}$$
2. The **edge density** $d_G(X, Y)$ is the fraction of possible edges present:
   $$d_G(X, Y) = \frac{e_G(X, Y)}{|X| |Y|}$$
   Clearly, $0 \le d_G(X, Y) \le 1$ for non-empty sets.

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
- `bipartiteEdgeCount_eq_card_interedges`: Bridge connecting `bipartiteEdgeCount` to Mathlib's `G.interedges`.
- `pairDensity_eq_edgeDensity`: Bridge connecting `pairDensity` to Mathlib's `SimpleGraph.edgeDensity`.
- `bipartiteEdgeCount_symm`, `pairDensity_symm`: Symmetry under swapping parts.
- `pairDensity_le_one`, `pairDensity_nonneg`: Boundedness in $[0, 1]$.
- `bipartiteEdgeCount_bot`, `pairDensity_bot`: Vanishing on the empty graph $\bot$.
- `bipartiteEdgeCount_top`, `pairDensity_top`: Maximality on the complete graph $\top$.
- `bipartiteEdgeCount_union_left`, `bipartiteEdgeCount_union_right`: Additivity over disjoint unions.
- `pairDensity_weighted_split`: Weighted average decomposition of densities under partition splitting.
- `IsEpsilonRegularPair`: The formal predicate for $\varepsilon$-regularity of a pair $(X, Y)$.
- `isEpsilonRegularPair_symm`: Symmetry of the $\varepsilon$-regularity predicate.

## References

- Szemerédi, E. (1978). *Regular partitions of graphs*. Problèmes Combinatoires et Théorie des Graphes, Colloq. Internat. CNRS, 260, 399–401.
- Komlós, J., & Simonovits, M. (1996). *Szemerédi's Regularity Lemma and its applications in graph theory*. Combinatorics, Paul Erdős is Eighty, 2, 295–352.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SzemerediRegularity

/-- The number of edges between two subsets $X, Y \subseteq V$ in a simple graph $G$. -/
def bipartiteEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℕ :=
  ((X ×ˢ Y).filter (fun p => G.Adj p.1 p.2)).card

/-- The edge density $d(X, Y) = \frac{e(X, Y)}{|X| |Y|}$ between sets $X, Y$. -/
noncomputable def pairDensity (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℝ :=
  (bipartiteEdgeCount G X Y : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))

/-! ### Mathlib Bridges -/

/-- Bridge: `bipartiteEdgeCount` coincides with the cardinality of Mathlib's `G.interedges X Y`. -/
theorem bipartiteEdgeCount_eq_card_interedges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    bipartiteEdgeCount G X Y = #(G.interedges X Y) := rfl

/-- Bridge: `pairDensity` coincides with the real coercion of Mathlib's `SimpleGraph.edgeDensity`. -/
theorem pairDensity_eq_edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    pairDensity G X Y = (G.edgeDensity X Y : ℝ) := by
  dsimp [pairDensity, SimpleGraph.edgeDensity, Rel.edgeDensity]
  push_cast
  rfl

/-! ### Vanishing on Empty Sets -/

@[simp]
theorem bipartiteEdgeCount_empty_left (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) :
    bipartiteEdgeCount G ∅ Y = 0 := by simp [bipartiteEdgeCount]

@[simp]
theorem bipartiteEdgeCount_empty_right (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    bipartiteEdgeCount G X ∅ = 0 := by simp [bipartiteEdgeCount]

@[simp]
theorem pairDensity_empty_left (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) :
    pairDensity G ∅ Y = 0 := by simp [pairDensity]

@[simp]
theorem pairDensity_empty_right (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    pairDensity G X ∅ = 0 := by simp [pairDensity]

/-! ### Symmetry -/

/-- Symmetry of bipartite edge count: $e(X, Y) = e(Y, X)$. -/
theorem bipartiteEdgeCount_symm (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    bipartiteEdgeCount G X Y = bipartiteEdgeCount G Y X := by
  have : Std.Symm G.Adj := ⟨fun _ _ => G.adj_symm⟩
  exact Rel.card_interedges_comm X Y

/-- Symmetry of pair density: $d(X, Y) = d(Y, X)$. -/
theorem pairDensity_symm (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    pairDensity G X Y = pairDensity G Y X := by
  dsimp [pairDensity]
  rw [bipartiteEdgeCount_symm G X Y, mul_comm (X.card : ℝ)]

/-! ### Bounds -/

/-- Bipartite edge count is bounded by the product of set cardinalities: $e(X, Y) \le |X| |Y|$. -/
theorem bipartiteEdgeCount_le_mul (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    bipartiteEdgeCount G X Y ≤ X.card * Y.card :=
  SimpleGraph.card_interedges_le_mul G X Y

/-- The edge density is bounded in $[0, 1]$ for non-empty sets. -/
theorem pairDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity G X Y ≤ 1 := by
  rw [pairDensity_eq_edgeDensity]
  exact_mod_cast G.edgeDensity_le_one X Y

/-- The edge density is non-negative. -/
theorem pairDensity_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    0 ≤ pairDensity G X Y := by
  rw [pairDensity_eq_edgeDensity]
  exact_mod_cast G.edgeDensity_nonneg X Y

/-! ### Monotonicity -/

/-- Subset monotonicity of bipartite edge count: $A \subseteq X, B \subseteq Y \implies e(A, B) \le e(X, Y)$. -/
theorem bipartiteEdgeCount_mono (G : SimpleGraph V) [DecidableRel G.Adj] {A B X Y : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ Y) :
    bipartiteEdgeCount G A B ≤ bipartiteEdgeCount G X Y :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.product_subset_product hA hB))

/-- Graph inclusion monotonicity of bipartite edge count: $G_1 \le G_2 \implies e_{G_1}(X, Y) \le e_{G_2}(X, Y)$. -/
theorem bipartiteEdgeCount_le_of_le {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hG : G₁ ≤ G₂) (X Y : Finset V) :
    bipartiteEdgeCount G₁ X Y ≤ bipartiteEdgeCount G₂ X Y :=
  Finset.card_le_card fun _ h => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h).1, hG (Finset.mem_filter.1 h).2⟩

/-! ### Extreme Graphs -/

/-- Bipartite edge count is zero in the empty graph $\bot$. -/
@[simp]
theorem bipartiteEdgeCount_bot (X Y : Finset V) :
    bipartiteEdgeCount (⊥ : SimpleGraph V) X Y = 0 := by
  simp [bipartiteEdgeCount]

/-- Pair density is zero in the empty graph $\bot$. -/
@[simp]
theorem pairDensity_bot (X Y : Finset V) :
    pairDensity (⊥ : SimpleGraph V) X Y = 0 := by
  simp [pairDensity]

/-- Bipartite edge count between disjoint sets in the complete graph $\top$ equals $|X| |Y|$. -/
theorem bipartiteEdgeCount_top {X Y : Finset V} (hdisj : Disjoint X Y) :
    bipartiteEdgeCount (⊤ : SimpleGraph V) X Y = X.card * Y.card := by
  rw [bipartiteEdgeCount, Finset.filter_true_of_mem, Finset.card_product]
  rintro ⟨u, v⟩ huv (rfl : u = v)
  exact Finset.disjoint_left.1 hdisj (Finset.mem_product.1 huv).1 (Finset.mem_product.1 huv).2

/-- Pair density between non-empty disjoint sets in the complete graph $\top$ equals $1$. -/
theorem pairDensity_top {X Y : Finset V} (hdisj : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity (⊤ : SimpleGraph V) X Y = 1 := by
  rw [pairDensity, bipartiteEdgeCount_top hdisj, Nat.cast_mul]
  have : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  exact div_self (by positivity)

/-! ### Independent Sets and Complete Bipartite Subgraphs -/

/-- If there are no edges between $X$ and $Y$, the edge count is 0. -/
theorem bipartiteEdgeCount_eq_zero_of_no_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    bipartiteEdgeCount G X Y = 0 := by
  rw [bipartiteEdgeCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨u, v⟩ huv
  exact hno u (Finset.mem_product.1 huv).1 v (Finset.mem_product.1 huv).2

/-- If there are no edges between $X$ and $Y$, the pair density is 0. -/
theorem pairDensity_eq_zero_of_no_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    pairDensity G X Y = 0 := by
  simp [pairDensity, bipartiteEdgeCount_eq_zero_of_no_edges G X Y hno]

/-- If all edges between disjoint $X$ and $Y$ are present, the edge count is $|X| |Y|$. -/
theorem bipartiteEdgeCount_eq_mul_of_all_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hall : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    bipartiteEdgeCount G X Y = X.card * Y.card := by
  rw [bipartiteEdgeCount, Finset.filter_true_of_mem, Finset.card_product]
  rintro ⟨u, v⟩ huv
  exact hall u (Finset.mem_product.1 huv).1 v (Finset.mem_product.1 huv).2

/-- If all edges between disjoint non-empty $X$ and $Y$ are present, the pair density is 1. -/
theorem pairDensity_eq_one_of_all_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hall : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity G X Y = 1 := by
  rw [pairDensity, bipartiteEdgeCount_eq_mul_of_all_edges G X Y hall, Nat.cast_mul]
  have : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
  have : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
  exact div_self (by positivity)

/-! ### Disjoint Additivity -/

/-- Bipartite edge count is additive on disjoint unions on the left. -/
theorem bipartiteEdgeCount_union_left (G : SimpleGraph V) [DecidableRel G.Adj] {X₁ X₂ Y : Finset V}
    (hdisj : Disjoint X₁ X₂) :
    bipartiteEdgeCount G (X₁ ∪ X₂) Y = bipartiteEdgeCount G X₁ Y + bipartiteEdgeCount G X₂ Y := by
  change (G.interedges (X₁ ∪ X₂) Y).card = (G.interedges X₁ Y).card + (G.interedges X₂ Y).card
  rw [SimpleGraph.interedges, Rel.interedges, Finset.union_product, Finset.filter_union]
  exact Finset.card_union_of_disjoint (SimpleGraph.interedges_disjoint_left G hdisj Y)

/-- Bipartite edge count is additive on disjoint unions on the right. -/
theorem bipartiteEdgeCount_union_right (G : SimpleGraph V) [DecidableRel G.Adj] {X Y₁ Y₂ : Finset V}
    (hdisj : Disjoint Y₁ Y₂) :
    bipartiteEdgeCount G X (Y₁ ∪ Y₂) = bipartiteEdgeCount G X Y₁ + bipartiteEdgeCount G X Y₂ := by
  rw [bipartiteEdgeCount_symm G X, bipartiteEdgeCount_union_left G hdisj,
      bipartiteEdgeCount_symm G Y₁ X, bipartiteEdgeCount_symm G Y₂ X]

/-- Weighted average split for pair density under partitioning the left set. -/
theorem pairDensity_weighted_split (G : SimpleGraph V) [DecidableRel G.Adj] {X₁ X₂ Y : Finset V}
    (hdisj : Disjoint X₁ X₂) (hU : (X₁ ∪ X₂).Nonempty) (hY : Y.Nonempty) :
    pairDensity G (X₁ ∪ X₂) Y =
      ((X₁.card : ℝ) / ((X₁ ∪ X₂).card : ℝ)) * pairDensity G X₁ Y +
      ((X₂.card : ℝ) / ((X₁ ∪ X₂).card : ℝ)) * pairDensity G X₂ Y := by
  rcases X₁.eq_empty_or_nonempty with rfl | hX₁
  · have hX₂ : X₂.Nonempty := by rwa [Finset.empty_union] at hU
    have : (X₂.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hX₂.card_pos)
    simp [pairDensity_empty_left, div_self this]
  rcases X₂.eq_empty_or_nonempty with rfl | hX₂
  · have hX₁ : X₁.Nonempty := by rwa [Finset.union_empty] at hU
    have : (X₁.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hX₁.card_pos)
    simp [pairDensity_empty_left, div_self this]
  have : ((X₁ ∪ X₂).card : ℝ) ≠ 0 := by positivity
  have : (Y.card : ℝ) ≠ 0 := by positivity
  have : (X₁.card : ℝ) ≠ 0 := by positivity
  have : (X₂.card : ℝ) ≠ 0 := by positivity
  dsimp [pairDensity]
  rw [bipartiteEdgeCount_union_left G hdisj]
  push_cast
  field_simp

/-! ### $\varepsilon$-Regular Pairs -/

/--
**Definition of an $\varepsilon$-Regular Pair**:
A pair $(X, Y)$ is $\varepsilon$-regular if for all $A \subseteq X$ with $|A| \ge \varepsilon |X|$
and all $B \subseteq Y$ with $|B| \ge \varepsilon |Y|$, the sub-pair density satisfies:
$$|d_G(A, B) - d_G(X, Y)| \le \varepsilon$$
-/
def IsEpsilonRegularPair (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (X Y : Finset V) : Prop :=
  ∀ (A : Finset V) (B : Finset V),
    A ⊆ X → B ⊆ Y →
    ε * (X.card : ℝ) ≤ (A.card : ℝ) →
    ε * (Y.card : ℝ) ≤ (B.card : ℝ) →
    |pairDensity G A B - pairDensity G X Y| ≤ ε

/-- Symmetry of the $\varepsilon$-regular pair predicate: $(X, Y)$ is $\varepsilon$-regular iff $(Y, X)$ is. -/
theorem isEpsilonRegularPair_symm (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (X Y : Finset V) :
    IsEpsilonRegularPair G ε X Y ↔ IsEpsilonRegularPair G ε Y X :=
  ⟨fun h B A hB hA hb ha => by rw [pairDensity_symm G B A, pairDensity_symm G Y X]; exact h A B hA hB ha hb,
   fun h A B hA hB ha hb => by rw [pairDensity_symm G A B, pairDensity_symm G X Y]; exact h B A hB hA hb ha⟩

/-- The edge density is unconditionally bounded by 1 for any pair of sets. -/
theorem pairDensity_le_one' (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    pairDensity G X Y ≤ 1 := by
  rw [pairDensity_eq_edgeDensity]
  exact_mod_cast G.edgeDensity_le_one X Y

/-- Any pair of sets is $1$-regular (and $\varepsilon$-regular for $\varepsilon \ge 1$). -/
theorem isEpsilonRegularPair_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (hε : 1 ≤ ε) (X Y : Finset V) :
    IsEpsilonRegularPair G ε X Y := fun A B _ _ _ _ => by
  rw [abs_le]
  constructor <;> linarith [pairDensity_nonneg G A B, pairDensity_le_one' G A B,
    pairDensity_nonneg G X Y, pairDensity_le_one' G X Y]

/-- Bridge: Mathlib's `SimpleGraph.IsUniform` implies `IsEpsilonRegularPair`. -/
theorem isEpsilonRegularPair_of_isUniform (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} {X Y : Finset V}
    (h : G.IsUniform ε X Y) :
    IsEpsilonRegularPair G ε X Y := fun A B hA hB ha hb => by
  rw [pairDensity_eq_edgeDensity, pairDensity_eq_edgeDensity]
  exact (h hA hB (by rwa [mul_comm]) (by rwa [mul_comm])).le

end SzemerediRegularity
