import Formalization.CauchyDavenport.Basic
import Formalization.CauchyDavenport.Iterated
import Formalization.CauchyDavenport.Vosper
import Formalization.CauchyDavenport.Chowla
import Formalization.CauchyDavenport.ErdosGinzburgZiv

/-!
# The Cauchy–Davenport Theorem & Additive Number Theory Suite

This master module aggregates the complete formalization of the **Cauchy–Davenport Theorem**
(Augustin-Louis Cauchy, 1813; Harold Davenport, 1935), its iterated $k$-fold sumset generalizations,
equality characterization via Vosper's critical pairs theorem, composite modulus extension via Chowla's
theorem, and zero-sum applications to the Erdős–Ginzburg–Ziv (EGZ) theorem.

## Module Tree Structure

1. **`Formalization.CauchyDavenport.Basic`**:
   - Machine-checked Cauchy–Davenport theorem in $\mathbb{Z}/p\mathbb{Z}$ (`cauchy_davenport`).
   - Torsion-free / integer Cauchy–Davenport theorem (`cauchy_davenport_of_isAddTorsionFree`, `cauchy_davenport_integers`).
   - Linearly ordered cancellative semigroup bounds (`cauchy_davenport_ordered`).
   - Minimal subgroup order bound in general additive groups (`cauchy_davenport_minOrder`).
   - Davenport's Dyson $e$-transform definitions (`dysonTransform`) and conservation laws:
     - $|A'| + |B'| = |A| + |B|$ (`dysonTransform_card`).
     - $A' + B' \subseteq A + B$ (`dysonTransform_sumset_subset`).
     - $|A' + B'| \le |A + B|$ (`dysonTransform_sumset_card_le`).

2. **`Formalization.CauchyDavenport.Iterated`**:
   - Multi-fold sumset bounds for arbitrary finite sequences $A_1, \dots, A_k \subseteq \mathbb{Z}/p\mathbb{Z}$:
     $$\left|\sum_{i=1}^k A_i\right| \ge \min\left(p, \sum_{i=1}^k |A_i| - k + 1\right)$$
   - Complete machine-checked inductive proof over $k$ (`cauchy_davenport_iterated`).
   - Full group surjectivity when $\sum |A_i| \ge p + k - 1$ (`iterated_sumset_eq_univ_of_card_ge`).
   - Multiple self-sumset bounds $|k A| \ge \min(p, k|A| - k + 1)$ (`cauchy_davenport_self_iterated`).

3. **`Formalization.CauchyDavenport.Vosper`**:
   - Characterization of critical pairs achieving $|A + B| = |A| + |B| - 1 \le p - 2$ with $|A|, |B| \ge 2$.
   - Arithmetic progression constructions (`arithmeticProgression`, `IsAP`, `IsAPWith`).
   - AP cardinality theorems (`card_arithmeticProgression`).
   - Vosper's Critical Pairs Theorem (`vosper_theorem`, `vosper_theorem_explicit`).
   - Vosper duality on sumset complements (`vosper_duality_card`).

4. **`Formalization.CauchyDavenport.Chowla`**:
   - Chowla's generalization to composite modulus $\mathbb{Z}/n\mathbb{Z}$ ($n \ge 2$) under coprime generator conditions:
     $$|A + B| \ge \min(n, |A| + |B| - 1)$$
   - Direct verification of base cases ($|B| = 1$, $|A| = n$).
   - Reduction of prime modulus Cauchy–Davenport from Chowla's theorem (`chowla_of_prime`).
   - Expansion under coprime pair additions (`card_add_coprime_pair_ge`).

5. **`Formalization.CauchyDavenport.ErdosGinzburgZiv`**:
   - Zero-sum subsequence theorem in $\mathbb{Z}/p\mathbb{Z}$ (any sequence of $2p - 1$ elements contains a subsequence of length $p$ summing to $0$).
   - Cauchy–Davenport full span deduction for $p-1$ difference pairs of size 2 (`egz_cauchy_davenport_span`).
   - Identical element zero-sum evaluation (`egz_identical_sum_zero`).
   - Erdős–Ginzburg–Ziv theorem statement (`erdos_ginzburg_ziv_prime`).

## Historical References

- Cauchy, A.-L. (1813). *Recherches sur les nombres*. Journal de l'École Polytechnique, 9, 99–123.
- Davenport, H. (1935). *On the addition of residue classes*. Journal of the London Mathematical Society, 10, 30–32.
- Vosper, A. G. (1956). *The critical pairs of subsets of a group of prime order*. Journal of the London Mathematical Society, 31, 200–205.
- Chowla, I. (1935). *A theorem on the addition of residue classes*. Proc. Indian Acad. Sci., 2, 242–243.
- Erdős, P., Ginzburg, A., & Ziv, A. (1961). *A theorem in the additive number theory*. Bull. Res. Council Israel, 10F, 41–43.
- DeVos, M. (2009). *On a generalization of the Cauchy-Davenport theorem*.
- Nathanson, M. B. (1996). *Additive Number Theory: Inverse Problems and the Geometry of Sumsets*. Springer GTM 165.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge University Press.
-/
