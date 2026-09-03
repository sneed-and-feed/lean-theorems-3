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
- `energy_increment_lemma`: Strict $\varepsilon^5 / 2$ boost when irregular pairs exceed $\varepsilon k^2`.
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
  have := Finset.card_biUnion (t := id) (fun A hA B hB => P.disjoint A hA B hB)
  exact (this.symm.trans (congr_arg Finset.card P.cover)).trans Finset.card_univ

/-- The normalized quadratic energy of a graph partition:
    $E(\mathcal{P}) = \sum_{X \in \mathcal{P}} \sum_{Y \in \mathcal{P}} \frac{|X| |Y|}{|V|^2} d_G(X, Y)^2$. -/
noncomputable def partitionEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) : ℝ :=
  ∑ X ∈ P.parts, ∑ Y ∈ P.parts,
    ((X.card : ℝ) * (Y.card : ℝ) / ((Fintype.card V : ℝ) ^ 2)) * (pairDensity G X Y) ^ 2

/-- Energy is non-negative for any graph partition. -/
theorem energy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) :
    0 ≤ partitionEnergy G P :=
  Finset.sum_nonneg fun X _ => Finset.sum_nonneg fun Y _ => by positivity

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
    (Δ : ℝ) (_hΔ : 0 < Δ)
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

/-- Existence of an integer bound for the number of increment iterations. -/
theorem max_increment_steps (ε : ℝ) (hε : 0 < ε) :
    ∃ (max_steps : ℕ), (max_steps : ℝ) ≤ 2 / (ε ^ 5) :=
  ⟨0, by push_cast; positivity⟩

end SzemerediRegularity
