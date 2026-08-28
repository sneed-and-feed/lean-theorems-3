import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Tactic.FieldSimp

open scoped BigOperators Finset
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SzemerediRegularity

/-- The number of edges between two subsets $X, Y \subseteq V$ in a simple graph $G$. -/
def bipartiteEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℕ :=
  ((X ×ˢ Y).filter (fun p => G.Adj p.1 p.2)).card

/-- The edge density $d(X, Y) = \frac{e(X, Y)}{|X| |Y|}$ between sets $X, Y$. -/
noncomputable def pairDensity (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℝ :=
  (bipartiteEdgeCount G X Y : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))

/-- Bridge: `pairDensity` coincides with the real coercion of Mathlib's `SimpleGraph.edgeDensity`. -/
theorem pairDensity_eq_edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    pairDensity G X Y = (G.edgeDensity X Y : ℝ) := by
  dsimp [pairDensity, SimpleGraph.edgeDensity, Rel.edgeDensity]
  push_cast
  rfl

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

/-- The edge density is non-negative. -/
theorem pairDensity_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    0 ≤ pairDensity G X Y := by
  rw [pairDensity_eq_edgeDensity]
  exact_mod_cast G.edgeDensity_nonneg X Y

/-- The edge density is bounded in $[0, 1]$ for non-empty sets. -/
theorem pairDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    pairDensity G X Y ≤ 1 := by
  rw [pairDensity_eq_edgeDensity]
  exact_mod_cast G.edgeDensity_le_one X Y

/-- The edge density is unconditionally bounded by 1 for any pair of sets. -/
theorem pairDensity_le_one' (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    pairDensity G X Y ≤ 1 := by
  rw [pairDensity_eq_edgeDensity]
  exact_mod_cast G.edgeDensity_le_one X Y

/-- Bipartite edge count is additive on disjoint unions on the left. -/
theorem bipartiteEdgeCount_union_left (G : SimpleGraph V) [DecidableRel G.Adj] {X₁ X₂ Y : Finset V}
    (hdisj : Disjoint X₁ X₂) :
    bipartiteEdgeCount G (X₁ ∪ X₂) Y = bipartiteEdgeCount G X₁ Y + bipartiteEdgeCount G X₂ Y := by
  change (G.interedges (X₁ ∪ X₂) Y).card = (G.interedges X₁ Y).card + (G.interedges X₂ Y).card
  rw [SimpleGraph.interedges, Rel.interedges, Finset.union_product, Finset.filter_union]
  exact Finset.card_union_of_disjoint (SimpleGraph.interedges_disjoint_left G hdisj Y)

@[simp]
theorem pairDensity_empty_left (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) :
    pairDensity G ∅ Y = 0 := by simp [pairDensity]

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

/-- A vertex partition of a finite graph $V$. -/
structure GraphPartition (V : Type*) [Fintype V] [DecidableEq V] where
  parts : Finset (Finset V)
  disjoint : ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B
  cover : parts.biUnion id = Finset.univ
  nonempty_parts : ∀ A ∈ parts, A.Nonempty

/-- The sum of cardinalities of all parts in a partition equals the total number of vertices $|V|$. -/
theorem GraphPartition.sum_card_parts (P : GraphPartition V) :
    ∑ X ∈ P.parts, X.card = Fintype.card V := by
  have := Finset.card_biUnion (t := id) (fun A hA B hB => P.disjoint A hA B hB)
  exact (this.symm.trans (congr_arg Finset.card P.cover)).trans Finset.card_univ

/-- The normalized quadratic energy of a graph partition:
    $E(\mathcal{P}) = \sum_{X \in \mathcal{P}} \sum_{Y \in \mathcal{P}} \frac{|X| |Y|}{|V|^2} d_G(X, Y)^2$. -/
noncomputable def partitionEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) : ℝ :=
  ∑ X ∈ P.parts, ∑ Y ∈ P.parts,
    ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) * (pairDensity G X Y) ^ 2

/--
**Energy Upper Bound**:
For any graph $G$ and partition $\mathcal{P}$, the normalized energy satisfies $E(\mathcal{P}) \le 1$.
-/
theorem energy_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) :
    partitionEnergy G P ≤ 1 := by
  rcases isEmpty_or_nonempty V with hV | ⟨v⟩
  · have : P.parts = ∅ := Finset.subset_empty.mp fun A hA => (P.nonempty_parts A hA).elim fun x _ => isEmptyElim x
    simp [partitionEnergy, this]
  have h_sum : ∑ X ∈ P.parts, (X.card : ℝ) = (Fintype.card V : ℝ) := by
    rw [← Nat.cast_sum, P.sum_card_parts]
  have h_term (X Y : Finset V) : ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) *
      (pairDensity G X Y) ^ 2 ≤ (X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2) := by
    have : (pairDensity G X Y) ^ 2 ≤ 1 := by
      nlinarith [pairDensity_nonneg G X Y, pairDensity_le_one' G X Y]
    nlinarith [show 0 ≤ (X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2) by positivity]
  refine (Finset.sum_le_sum fun X _ => Finset.sum_le_sum fun Y _ => h_term X Y).trans ?_
  simp_rw [← Finset.sum_div, ← Finset.sum_mul_sum, h_sum]
  have : (Fintype.card V : ℝ) * (Fintype.card V : ℝ) = (Fintype.card V : ℝ) ^ 2 := by ring
  rw [this, div_self (by positivity)]

/--
**Energy Exhaustion Principle**:
Any energy sequence bounded in $[0, 1]$ with strict minimum increment $\Delta > 0$
at each step can make at most $\lfloor 1 / \Delta \rfloor$ steps.
-/
theorem energy_exhaustion_bound (energy_seq : ℕ → ℝ)
    (h_nonneg : ∀ (i : ℕ), 0 ≤ energy_seq i)
    (h_le_one : ∀ (i : ℕ), energy_seq i ≤ 1)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (h_inc : ∀ (i : ℕ), energy_seq i + Δ ≤ energy_seq (i + 1)) (k : ℕ) :
    (k : ℝ) * Δ ≤ 1 := by
  have h_step (i : ℕ) : (i : ℝ) * Δ ≤ energy_seq i := by
    induction i with
    | zero => simpa using h_nonneg 0
    | succ n ih => push_cast; linarith [h_inc n]
  exact (h_step k).trans (h_le_one k)

/--
**Maximum Number of Increment Iterations**:
The maximum number of times the energy increment can occur under an $\varepsilon^5 / 2$ step boost
is bounded by $2 / \varepsilon^5$.
-/
theorem max_increment_steps_bound (energy_seq : ℕ → ℝ)
    (h_nonneg : ∀ (i : ℕ), 0 ≤ energy_seq i)
    (h_le_one : ∀ (i : ℕ), energy_seq i ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (h_inc : ∀ (i : ℕ), energy_seq i + (ε ^ 5) / 2 ≤ energy_seq (i + 1)) (k : ℕ) :
    (k : ℝ) ≤ 2 / (ε ^ 5) := by
  have h_bound := energy_exhaustion_bound energy_seq h_nonneg h_le_one ((ε ^ 5) / 2) (by positivity) h_inc k
  have : 0 < ε ^ 5 := by positivity
  rw [le_div_iff₀ this]
  linarith

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

end SzemerediRegularity
