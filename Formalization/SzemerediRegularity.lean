import Formalization.SzemerediRegularity.PairDensity
import Formalization.SzemerediRegularity.EnergyIncrement
import Formalization.SzemerediRegularity.RegularityLemma

/-!
# Szemerédi's Regularity Lemma & Partition Calculus

This module aggregates the complete formalization package for **Szemerédi's Regularity Lemma**:
1. `PairDensity.lean`: Pair edge density $d(X, Y) = e(X, Y) / (|X| |Y|)$ and $\varepsilon$-regular pairs.
2. `EnergyIncrement.lean`: Mean-square partition energy $E(\mathcal{P})$, Cauchy–Schwarz monotonicity, and the Energy Increment Lemma delivering $+\varepsilon^5/2$ energy per step.
3. `RegularityLemma.lean`: Szemerédi's Regularity Lemma, the Triangle Counting Lemma, the Triangle Removal Lemma, and graph-theoretic deduction of Roth's theorem.

## References
- Szemerédi, E. (1978). *Regular partitions of graphs*.
- Ruzsa, I. Z., & Szemerédi, E. (1978). *Triple systems with no six points carrying three triangles*.
- Gowers, W. T. (1997). *Lower bounds of tower type for Szemerédi's regularity lemma*.
- Fox, J. (2011). *A new proof of the graph removal lemma*.
-/
