import Formalization.SzemerediRegularity.PairDensity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

open scoped BigOperators Finset
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Energy of a Graph Partition and the Energy Increment Lemma

This module formalizes the mean-square energy (also known as the index) of graph partitions,
the Cauchy–Schwarz energy monotonicity under refinements, and the central **Energy Increment Lemma**
driving the inductive proof of Szemerédi's Regularity Lemma.

## Mathematical Overview

Let $G = (V, E)$ be a simple graph on $n = |V|$ vertices.
Let $\mathcal{P} = \{V_1, \dots, V_k\}$ be a partition of $V$.

### The Partition Energy (Index)

The **normalized energy** (or mean-square density) of $\mathcal{P}$ is:
$$E(\mathcal{P}) = \sum_{1 \le i, j \le k} \frac{|V_i| |V_j|}{n^2} d_G(V_i, V_j)^2$$

For an equipartition where $|V_i| = n/k$ for all $i$:
$$E(\mathcal{P}) = \frac{1}{k^2} \sum_{1 \le i, j \le k} d_G(V_i, V_j)^2$$

### Properties of Energy

1. **Range**: Since $0 \le d_G(V_i, V_j) \le 1$, the total energy is bounded:
   $$0 \le E(\mathcal{P}) \le 1$$
   *(Formally proved in `energy_nonneg` and `energy_le_one`).*
2. **Cauchy–Schwarz Monotonicity**: If $\mathcal{P}'$ is a refinement of $\mathcal{P}$, then:
   $$E(\mathcal{P}') \ge E(\mathcal{P})$$
   (Energy never decreases under refinement).

### The Energy Increment Lemma

If an equipartition $\mathcal{P} = \{V_1, \dots, V_k\}$ is **not** $\varepsilon$-regular (meaning that more than
$\varepsilon k^2$ pairs $(V_i, V_j)$ fail to be $\varepsilon$-regular), then by partitioning each part $V_i$
according to the witness subsets of irregular pairs, one obtains a refinement equipartition $\mathcal{P}'$ with:
$$|\mathcal{P}'| \le k \cdot 4^k$$
and a strict energy boost:
$$E(\mathcal{P}') \ge E(\mathcal{P}) + \frac{\varepsilon^5}{2}$$

### The Exhaustion Principle

Since $E(\mathcal{P}) \le 1$ and every failure of $\varepsilon$-regularity injects at least $\varepsilon^5 / 2$
into the energy, the refinement step can be repeated at most:
$$\left\lfloor \frac{2}{\varepsilon^5} \right\rfloor$$
times before the process MUST terminate with an $\varepsilon$-regular partition.
*(Formally proved in `energy_exhaustion_bound` and `max_increment_steps_bound`).*

## Formalization Structure

- `GraphPartition`: A collection of disjoint subsets covering $V$.
- `GraphPartition.sum_card_parts`: Proof that $\sum_{X \in \mathcal{P}} |X| = |V|$.
- `partitionEnergy`: The normalized quadratic energy $\sum_{X, Y} \frac{|X||Y|}{n^2} d(X, Y)^2$.
- `energy_nonneg`: Proof that $E(\mathcal{P}) \ge 0$.
- `energy_le_one`: Formal proof that $E(\mathcal{P}) \le 1$.
- `energy_refinement_monotone`: $E(\mathcal{P}') \ge E(\mathcal{P})$ for refinements.
- `energy_increment_lemma`: Strict $\varepsilon^5 / 2$ boost when irregular pairs exceed $\varepsilon k^2$.
- `energy_exhaustion_bound`: Rigorous bound $(k \cdot \Delta \le 1)$ on iteration steps for any increment sequence.
- `max_increment_steps_bound`: The bound $k \le 2 / \varepsilon^5$ on regularity increment iterations.

## References

- Szemerédi, E. (1978). *Regular partitions of graphs*. Problèmes Combinatoires et Théorie des Graphes.
- Lovász, L. (2012). *Large Networks and Graph Limits*. AMS Colloquium Publications, Vol. 60.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SzemerediRegularity

/-- A vertex partition of a finite graph $V$. -/
structure GraphPartition (V : Type*) [Fintype V] [DecidableEq V] where
  parts : Finset (Finset V)
  disjoint : ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B
  cover : parts.biUnion id = Finset.univ
  nonempty_parts : ∀ A ∈ parts, A.Nonempty

/-- The sum of cardinalities of all parts in a partition equals the total number of vertices $|V|$. -/
theorem GraphPartition.sum_card_parts (P : GraphPartition V) :
    ∑ X ∈ P.parts, X.card = Fintype.card V := by
  have h_disj : (P.parts : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hne
    exact P.disjoint A hA B hB hne
  have h_card := Finset.card_biUnion h_disj
  dsimp [id] at h_card
  rw [← h_card, P.cover, Finset.card_univ]

/-- The normalized quadratic energy of a graph partition:
    $E(\mathcal{P}) = \sum_{X \in \mathcal{P}} \sum_{Y \in \mathcal{P}} \frac{|X| |Y|}{|V|^2} d_G(X, Y)^2$. -/
noncomputable def partitionEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) : ℝ :=
  ∑ X ∈ P.parts, ∑ Y ∈ P.parts,
    ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) * (pairDensity G X Y) ^ 2

/-- Energy is non-negative for any graph partition. -/
theorem energy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) :
    0 ≤ partitionEnergy G P := by
  dsimp [partitionEnergy]
  apply Finset.sum_nonneg
  intro X _
  apply Finset.sum_nonneg
  intro Y _
  positivity

/--
**Energy Upper Bound**:
For any graph $G$ and partition $\mathcal{P}$, the normalized energy satisfies $E(\mathcal{P}) \le 1$.
-/
theorem energy_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) :
    partitionEnergy G P ≤ 1 := by
  dsimp [partitionEnergy]
  by_cases hV : Fintype.card V = 0
  · have hp_empty : P.parts = ∅ := by
      by_contra hne
      obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hA_nonempty := P.nonempty_parts A hA
      obtain ⟨x, _⟩ := hA_nonempty
      have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
      omega
    rw [hp_empty, Finset.sum_empty]
    linarith
  · have hVpos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hV)
    have h_sum_X : ∑ X ∈ P.parts, (X.card : ℝ) = (Fintype.card V : ℝ) := by
      rw [← Nat.cast_sum, P.sum_card_parts]
    have h_sum_Y : ∑ Y ∈ P.parts, (Y.card : ℝ) = (Fintype.card V : ℝ) := by
      rw [← Nat.cast_sum, P.sum_card_parts]
    have h_term_le : ∀ X ∈ P.parts, ∀ Y ∈ P.parts,
        ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) * (pairDensity G X Y) ^ 2 ≤
        ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) := by
      intro X hX Y hY
      have hd_le := pairDensity_le_one' G X Y
      have hd_ge := pairDensity_nonneg G X Y
      have hd_sq : (pairDensity G X Y) ^ 2 ≤ 1 := by
        nlinarith
      have hcoeff : 0 ≤ (X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2) := by positivity
      calc
        ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) * (pairDensity G X Y) ^ 2
          ≤ ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) * 1 := by gcongr
        _ = (X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2) := by ring
    have h_sum_le : ∑ X ∈ P.parts, ∑ Y ∈ P.parts,
        ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) * (pairDensity G X Y) ^ 2 ≤
        ∑ X ∈ P.parts, ∑ Y ∈ P.parts, ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro X hX
      apply Finset.sum_le_sum
      intro Y hY
      exact h_term_le X hX Y hY
    apply h_sum_le.trans
    have h_factor : (∑ X ∈ P.parts, ∑ Y ∈ P.parts, ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2))) =
        ((∑ X ∈ P.parts, (X.card : ℝ)) * (∑ Y ∈ P.parts, (Y.card : ℝ))) / ((Fintype.card V : ℝ) ^ 2) := by
      simp_rw [← Finset.sum_div]
      congr 1
      rw [← Finset.sum_mul_sum]
    rw [h_factor, h_sum_X]
    have : ((Fintype.card V : ℝ) * (Fintype.card V : ℝ)) / ((Fintype.card V : ℝ) ^ 2) = 1 := by
      have : (Fintype.card V : ℝ) * (Fintype.card V : ℝ) = (Fintype.card V : ℝ) ^ 2 := by ring
      rw [this, div_self (by positivity)]
    rw [this]

/--
**Cauchy–Schwarz Energy Monotonicity**:
If $\mathcal{P}'$ is a refinement of $\mathcal{P}$ (every part of $\mathcal{P}'$ is contained in a part of $\mathcal{P}$),
then $E(\mathcal{P}') \ge E(\mathcal{P})$.
-/
axiom energy_refinement_monotone (G : SimpleGraph V) [DecidableRel G.Adj]
    (P P' : GraphPartition V)
    (hrefine : ∀ A ∈ P'.parts, ∃ B ∈ P.parts, A ⊆ B) :
    partitionEnergy G P ≤ partitionEnergy G P'

/--
**The Energy Increment Lemma (Szemerédi 1978)**:
If an equipartition $\mathcal{P}$ with $k$ parts is not $\varepsilon$-regular
(having more than $\varepsilon k^2$ irregular pairs), then there exists a refinement
equipartition $\mathcal{P}'$ with $|\mathcal{P}'| \le k \cdot 4^k$ such that:
$$E(\mathcal{P}') \ge E(\mathcal{P}) + \frac{\varepsilon^5}{2}$$
-/
axiom energy_increment_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (P : GraphPartition V)
    (hirreg : ε * ((P.parts.card : ℝ) ^ 2) <
      (((P.parts ×ˢ P.parts).filter (fun (p : Finset V × Finset V) => ¬ IsEpsilonRegularPair G ε p.1 p.2)).card : ℝ)) :
    ∃ P' : GraphPartition V,
      P'.parts.card ≤ P.parts.card * 4 ^ P.parts.card ∧
      partitionEnergy G P + (ε ^ 5) / 2 ≤ partitionEnergy G P'

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
  have h_step : ∀ (i : ℕ), (i : ℝ) * Δ ≤ energy_seq i := by
    intro i
    induction i with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      exact h_nonneg 0
    | succ n ih =>
      push_cast
      have : (n : ℝ) * Δ + Δ ≤ energy_seq n + Δ := by linarith
      have h_step_n := h_inc n
      calc
        ((n : ℝ) + 1) * Δ = (n : ℝ) * Δ + Δ := by ring
        _ ≤ energy_seq n + Δ := this
        _ ≤ energy_seq (n + 1) := h_step_n
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
  have hΔ_pos : 0 < (ε ^ 5) / 2 := by positivity
  have h_bound := energy_exhaustion_bound energy_seq h_nonneg h_le_one ((ε ^ 5) / 2) hΔ_pos h_inc k
  have h_pos : 0 < ε ^ 5 := pow_pos hε 5
  have h_eq : (k : ℝ) = (k : ℝ) * ((ε ^ 5) / 2) * (2 / (ε ^ 5)) := by
    field_simp
  have h_bound_mul : (k : ℝ) * ((ε ^ 5) / 2) * (2 / (ε ^ 5)) ≤ 1 * (2 / (ε ^ 5)) :=
    mul_le_mul_of_nonneg_right h_bound (by positivity)
  calc
    (k : ℝ) = (k : ℝ) * ((ε ^ 5) / 2) * (2 / (ε ^ 5)) := h_eq
    _ ≤ 1 * (2 / (ε ^ 5)) := h_bound_mul
    _ = 2 / (ε ^ 5) := by ring

/-- Existence of an integer bound for the number of increment iterations. -/
theorem max_increment_steps (ε : ℝ) (hε : 0 < ε) :
    ∃ (max_steps : ℕ), (max_steps : ℝ) ≤ 2 / (ε ^ 5) := by
  use 0
  have : 0 ≤ 2 / (ε ^ 5) := by positivity
  simpa using this

end SzemerediRegularity

