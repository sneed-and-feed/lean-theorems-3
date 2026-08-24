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
    bipartiteEdgeCount G ∅ Y = 0 := by
  dsimp [bipartiteEdgeCount]
  simp

@[simp]
theorem bipartiteEdgeCount_empty_right (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    bipartiteEdgeCount G X ∅ = 0 := by
  dsimp [bipartiteEdgeCount]
  simp

@[simp]
theorem pairDensity_empty_left (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) :
    pairDensity G ∅ Y = 0 := by
  dsimp [pairDensity]
  simp

@[simp]
theorem pairDensity_empty_right (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    pairDensity G X ∅ = 0 := by
  dsimp [pairDensity]
  simp

/-! ### Symmetry -/

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

/-! ### Bounds -/

/-- Bipartite edge count is bounded by the product of set cardinalities: $e(X, Y) \le |X| |Y|$. -/
theorem bipartiteEdgeCount_le_mul (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    bipartiteEdgeCount G X Y ≤ X.card * Y.card := by
  dsimp [bipartiteEdgeCount]
  have h_sub : (X ×ˢ Y).filter (fun p => G.Adj p.1 p.2) ⊆ X ×ˢ Y := Finset.filter_subset _ _
  have h_card := Finset.card_le_card h_sub
  rwa [Finset.card_product] at h_card

/-- The edge density is bounded in $[0, 1]$ for non-empty sets. -/
theorem pairDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity G X Y ≤ 1 := by
  dsimp [pairDensity]
  have h_le := bipartiteEdgeCount_le_mul G X Y
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

/-! ### Monotonicity -/

/-- Subset monotonicity of bipartite edge count: $A \subseteq X, B \subseteq Y \implies e(A, B) \le e(X, Y)$. -/
theorem bipartiteEdgeCount_mono (G : SimpleGraph V) [DecidableRel G.Adj] {A B X Y : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ Y) :
    bipartiteEdgeCount G A B ≤ bipartiteEdgeCount G X Y := by
  dsimp [bipartiteEdgeCount]
  apply Finset.card_le_card
  intro ⟨u, v⟩ huv
  simp only [Finset.mem_filter, Finset.mem_product] at huv ⊢
  exact ⟨⟨hA huv.1.1, hB huv.1.2⟩, huv.2⟩

/-- Graph inclusion monotonicity of bipartite edge count: $G_1 \le G_2 \implies e_{G_1}(X, Y) \le e_{G_2}(X, Y)$. -/
theorem bipartiteEdgeCount_le_of_le {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hG : G₁ ≤ G₂) (X Y : Finset V) :
    bipartiteEdgeCount G₁ X Y ≤ bipartiteEdgeCount G₂ X Y := by
  dsimp [bipartiteEdgeCount]
  apply Finset.card_le_card
  intro ⟨u, v⟩ huv
  simp only [Finset.mem_filter, Finset.mem_product] at huv ⊢
  exact ⟨huv.1, hG huv.2⟩

/-! ### Extreme Graphs -/

/-- Bipartite edge count is zero in the empty graph $\bot$. -/
@[simp]
theorem bipartiteEdgeCount_bot (X Y : Finset V) :
    bipartiteEdgeCount (⊥ : SimpleGraph V) X Y = 0 := by
  dsimp [bipartiteEdgeCount]
  have : (X ×ˢ Y).filter (fun p => (⊥ : SimpleGraph V).Adj p.1 p.2) = ∅ := by
    ext ⟨u, v⟩
    simp
  rw [this, Finset.card_empty]

/-- Pair density is zero in the empty graph $\bot$. -/
@[simp]
theorem pairDensity_bot (X Y : Finset V) :
    pairDensity (⊥ : SimpleGraph V) X Y = 0 := by
  dsimp [pairDensity]
  rw [bipartiteEdgeCount_bot, Nat.cast_zero, zero_div]

/-- Bipartite edge count between disjoint sets in the complete graph $\top$ equals $|X| |Y|$. -/
theorem bipartiteEdgeCount_top {X Y : Finset V} (hdisj : Disjoint X Y) :
    bipartiteEdgeCount (⊤ : SimpleGraph V) X Y = X.card * Y.card := by
  dsimp [bipartiteEdgeCount]
  have : (X ×ˢ Y).filter (fun p => (⊤ : SimpleGraph V).Adj p.1 p.2) = X ×ˢ Y := by
    apply Finset.filter_true_of_mem
    intro ⟨u, v⟩ huv
    simp only [Finset.mem_product, SimpleGraph.top_adj] at huv ⊢
    rintro rfl
    exact Finset.disjoint_left.mp hdisj huv.1 huv.2
  rw [this, Finset.card_product]

/-- Pair density between non-empty disjoint sets in the complete graph $\top$ equals $1$. -/
theorem pairDensity_top {X Y : Finset V} (hdisj : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity (⊤ : SimpleGraph V) X Y = 1 := by
  dsimp [pairDensity]
  rw [bipartiteEdgeCount_top hdisj, Nat.cast_mul]
  have hpos : (X.card : ℝ) * (Y.card : ℝ) ≠ 0 := by
    have : 0 < (X.card : ℝ) * (Y.card : ℝ) := by
      have hXpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
      have hYpos : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
      positivity
    exact ne_of_gt this
  exact div_self hpos

/-! ### Independent Sets and Complete Bipartite Subgraphs -/

/-- If there are no edges between $X$ and $Y$, the edge count is 0. -/
theorem bipartiteEdgeCount_eq_zero_of_no_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    bipartiteEdgeCount G X Y = 0 := by
  dsimp [bipartiteEdgeCount]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨u, v⟩ huv
  simp only [Finset.mem_product] at huv
  exact hno u huv.1 v huv.2

/-- If there are no edges between $X$ and $Y$, the pair density is 0. -/
theorem pairDensity_eq_zero_of_no_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    pairDensity G X Y = 0 := by
  dsimp [pairDensity]
  rw [bipartiteEdgeCount_eq_zero_of_no_edges G X Y hno, Nat.cast_zero, zero_div]

/-- If all edges between disjoint $X$ and $Y$ are present, the edge count is $|X| |Y|$. -/
theorem bipartiteEdgeCount_eq_mul_of_all_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hall : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    bipartiteEdgeCount G X Y = X.card * Y.card := by
  dsimp [bipartiteEdgeCount]
  have : (X ×ˢ Y).filter (fun p => G.Adj p.1 p.2) = X ×ˢ Y := by
    apply Finset.filter_true_of_mem
    intro ⟨u, v⟩ huv
    simp only [Finset.mem_product] at huv
    exact hall u huv.1 v huv.2
  rw [this, Finset.card_product]

/-- If all edges between disjoint non-empty $X$ and $Y$ are present, the pair density is 1. -/
theorem pairDensity_eq_one_of_all_edges (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hall : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity G X Y = 1 := by
  dsimp [pairDensity]
  rw [bipartiteEdgeCount_eq_mul_of_all_edges G X Y hall, Nat.cast_mul]
  have hpos : (X.card : ℝ) * (Y.card : ℝ) ≠ 0 := by
    have : 0 < (X.card : ℝ) * (Y.card : ℝ) := by
      have hXpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hX.card_pos
      have hYpos : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
      positivity
    exact ne_of_gt this
  exact div_self hpos

/-! ### Disjoint Additivity -/

/-- Bipartite edge count is additive on disjoint unions on the left. -/
theorem bipartiteEdgeCount_union_left (G : SimpleGraph V) [DecidableRel G.Adj] {X₁ X₂ Y : Finset V}
    (hdisj : Disjoint X₁ X₂) :
    bipartiteEdgeCount G (X₁ ∪ X₂) Y = bipartiteEdgeCount G X₁ Y + bipartiteEdgeCount G X₂ Y := by
  dsimp [bipartiteEdgeCount]
  rw [Finset.union_product, Finset.filter_union, Finset.card_union_of_disjoint]
  apply Finset.disjoint_filter_filter
  rw [Finset.disjoint_left]
  rintro ⟨u, v⟩ h1 h2
  rw [Finset.mem_product] at h1 h2
  exact Finset.disjoint_left.mp hdisj h1.1 h2.1

/-- Bipartite edge count is additive on disjoint unions on the right. -/
theorem bipartiteEdgeCount_union_right (G : SimpleGraph V) [DecidableRel G.Adj] {X Y₁ Y₂ : Finset V}
    (hdisj : Disjoint Y₁ Y₂) :
    bipartiteEdgeCount G X (Y₁ ∪ Y₂) = bipartiteEdgeCount G X Y₁ + bipartiteEdgeCount G X Y₂ := by
  rw [bipartiteEdgeCount_symm G X (Y₁ ∪ Y₂), bipartiteEdgeCount_union_left G hdisj,
      bipartiteEdgeCount_symm G Y₁ X, bipartiteEdgeCount_symm G Y₂ X]

/-- Weighted average split for pair density under partitioning the left set. -/
theorem pairDensity_weighted_split (G : SimpleGraph V) [DecidableRel G.Adj] {X₁ X₂ Y : Finset V}
    (hdisj : Disjoint X₁ X₂) (hU : (X₁ ∪ X₂).Nonempty) (hY : Y.Nonempty) :
    pairDensity G (X₁ ∪ X₂) Y =
      ((X₁.card : ℝ) / ((X₁ ∪ X₂).card : ℝ)) * pairDensity G X₁ Y +
      ((X₂.card : ℝ) / ((X₁ ∪ X₂).card : ℝ)) * pairDensity G X₂ Y := by
  by_cases hX₁ : X₁.Nonempty
  · by_cases hX₂ : X₂.Nonempty
    · dsimp [pairDensity]
      rw [bipartiteEdgeCount_union_left G hdisj]
      push_cast
      have hUcard : ((X₁ ∪ X₂).card : ℝ) ≠ 0 := by
        have : 0 < ((X₁ ∪ X₂).card : ℝ) := Nat.cast_pos.mpr hU.card_pos
        exact ne_of_gt this
      have hYcard : (Y.card : ℝ) ≠ 0 := by
        have : 0 < (Y.card : ℝ) := Nat.cast_pos.mpr hY.card_pos
        exact ne_of_gt this
      have hX₁card : (X₁.card : ℝ) ≠ 0 := by
        have : 0 < (X₁.card : ℝ) := Nat.cast_pos.mpr hX₁.card_pos
        exact ne_of_gt this
      have hX₂card : (X₂.card : ℝ) ≠ 0 := by
        have : 0 < (X₂.card : ℝ) := Nat.cast_pos.mpr hX₂.card_pos
        exact ne_of_gt this
      have : ((bipartiteEdgeCount G X₁ Y : ℝ) + (bipartiteEdgeCount G X₂ Y : ℝ)) / (((X₁ ∪ X₂).card : ℝ) * (Y.card : ℝ)) =
          ((X₁.card : ℝ) / ((X₁ ∪ X₂).card : ℝ)) * ((bipartiteEdgeCount G X₁ Y : ℝ) / ((X₁.card : ℝ) * (Y.card : ℝ))) +
          ((X₂.card : ℝ) / ((X₁ ∪ X₂).card : ℝ)) * ((bipartiteEdgeCount G X₂ Y : ℝ) / ((X₂.card : ℝ) * (Y.card : ℝ))) := by
        field_simp
      exact this
    · have hX₂e : X₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX₂
      subst hX₂e
      rw [Finset.union_empty, pairDensity_empty_left]
      have : ((X₁.card : ℝ) ≠ 0) := by
        have : 0 < (X₁.card : ℝ) := Nat.cast_pos.mpr hX₁.card_pos
        exact ne_of_gt this
      rw [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul, add_zero, div_self this, one_mul]
  · have hX₁e : X₁ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX₁
    subst hX₁e
    rw [Finset.empty_union, pairDensity_empty_left]
    have hX₂ : X₂.Nonempty := by rwa [Finset.empty_union] at hU
    have : ((X₂.card : ℝ) ≠ 0) := by
      have : 0 < (X₂.card : ℝ) := Nat.cast_pos.mpr hX₂.card_pos
      exact ne_of_gt this
    rw [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul, zero_add, div_self this, one_mul]

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
    IsEpsilonRegularPair G ε X Y ↔ IsEpsilonRegularPair G ε Y X := by
  constructor
  · intro h B A hB hA hBcard hAcard
    rw [pairDensity_symm G B A, pairDensity_symm G Y X]
    exact h A B hA hB hAcard hBcard
  · intro h A B hA hB hAcard hBcard
    rw [pairDensity_symm G A B, pairDensity_symm G X Y]
    exact h B A hB hA hBcard hAcard

/-- The edge density is unconditionally bounded by 1 for any pair of sets. -/
theorem pairDensity_le_one' (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    pairDensity G X Y ≤ 1 := by
  by_cases hX : X.Nonempty
  · by_cases hY : Y.Nonempty
    · exact pairDensity_le_one G X Y hX hY
    · have : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
      subst this
      rw [pairDensity_empty_right]
      linarith
  · have : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    subst this
    rw [pairDensity_empty_left]
    linarith

/-- Any pair of sets is $1$-regular (and $\varepsilon$-regular for $\varepsilon \ge 1$). -/
theorem isEpsilonRegularPair_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (hε : 1 ≤ ε) (X Y : Finset V) :
    IsEpsilonRegularPair G ε X Y := by
  intro A B _ _ _ _
  have h1 : 0 ≤ pairDensity G A B := pairDensity_nonneg G A B
  have h2 : pairDensity G A B ≤ 1 := pairDensity_le_one' G A B
  have h3 : 0 ≤ pairDensity G X Y := pairDensity_nonneg G X Y
  have h4 : pairDensity G X Y ≤ 1 := pairDensity_le_one' G X Y
  rw [abs_le]
  constructor <;> linarith

/-- Bridge: Mathlib's `SimpleGraph.IsUniform` implies `IsEpsilonRegularPair`. -/
theorem isEpsilonRegularPair_of_isUniform (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} {X Y : Finset V}
    (h : G.IsUniform ε X Y) :
    IsEpsilonRegularPair G ε X Y := by
  intro A B hA hB hAcard hBcard
  have h_lt := h hA hB (by rwa [mul_comm]) (by rwa [mul_comm])
  rw [pairDensity_eq_edgeDensity, pairDensity_eq_edgeDensity]
  exact h_lt.le

end SzemerediRegularity

