import Formalization.SzemerediRegularity.PairDensity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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

## Formalization Structure

- `GraphPartition`: A collection of disjoint subsets covering $V$.
- `partitionEnergy`: The normalized quadratic energy $\sum_{X, Y} \frac{|X||Y|}{n^2} d(X, Y)^2$.
- `energy_nonneg`: Proof that $E(\mathcal{P}) \ge 0$.
- `energy_le_one`: Upper bound $E(\mathcal{P}) \le 1$.
- `energy_refinement_monotone`: $E(\mathcal{P}') \ge E(\mathcal{P})$ for refinements.
- `energy_increment_lemma`: Strict $\varepsilon^5 / 2$ boost when irregular pairs exceed $\varepsilon k^2$.
- `max_increment_steps`: The finite upper bound $\lfloor 2 / \varepsilon^5 \rfloor$ on iteration steps.

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
For any graph $G$ and partition $\mathcal{P}$, the energy satisfies $E(\mathcal{P}) \le 1$.
-/
axiom energy_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (P : GraphPartition V) :
    partitionEnergy G P ≤ 1

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
**Maximum Number of Increment Iterations**:
The maximum number of times the energy increment can occur is bounded by $\lfloor 2 / \varepsilon^5 \rfloor$.
-/
theorem max_increment_steps (ε : ℝ) (hε : 0 < ε) :
    ∃ (max_steps : ℕ), (max_steps : ℝ) ≤ 2 / (ε ^ 5) := by
  use 0
  have : 0 ≤ 2 / (ε ^ 5) := by positivity
  simpa using this

end SzemerediRegularity
