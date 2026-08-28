import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.ETransform
import Mathlib.GroupTheory.Order.Min
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Cauchy–Davenport Theorem and Iterated Sumset Bounds

This module formalizes the **Cauchy–Davenport Theorem** (Augustin-Louis Cauchy 1813, Harold Davenport 1935),
its extensions to iterated sumsets $\sum_{i=1}^k A_i$, Dyson $e$-transforms, and the full span lemma
for the Erdős–Ginzburg–Ziv theorem.

## Mathematical Overview

1. **Prime Cyclic Groups $\mathbb{Z}/p\mathbb{Z}$**:
   $$|A + B| \ge \min(p, |A| + |B| - 1)$$
2. **Torsion-Free Groups & Integers $\mathbb{Z}$**:
   $$|A + B| \ge |A| + |B| - 1$$
3. **Iterated Sumsets**:
   $$\left| \sum_{i=1}^k A_i \right| \ge \min\left(p, \sum_{i=1}^k |A_i| - k + 1\right)$$
4. **Full Group Surjectivity**:
   If $\sum_{i=1}^k |A_i| \ge p + k - 1$, then $\sum_{i=1}^k A_i = \mathbb{Z}/p\mathbb{Z}$.
5. **Dyson $e$-transforms**: Conservation $|A'| + |B'| = |A| + |B|$ and sumset inclusion $A' + B' \subseteq A + B$.

## References

- Cauchy, A.-L. (1813). *Recherches sur les nombres*. Journal de l'École Polytechnique, 9, 99–123.
- Davenport, H. (1935). *On the addition of residue classes*. Journal of the London Mathematical Society, 10, 30–32.
- Erdős, P., Ginzburg, A., & Ziv, A. (1961). *A theorem in the additive number theory*. Bull. Res. Council Israel, 10F, 41–43.
-/

namespace CauchyDavenport

variable {G : Type*} [DecidableEq G]

/-- The first component of the Dyson transform: $A' = A \cup (e +ᵥ B)$. -/
def dysonTransformFst [AddCommGroup G] (e : G) (A B : Finset G) : Finset G :=
  A ∪ (e +ᵥ B)

/-- The second component of the Dyson transform: $B' = B \cap (-e +ᵥ A)$. -/
def dysonTransformSnd [AddCommGroup G] (e : G) (A B : Finset G) : Finset G :=
  B ∩ (-e +ᵥ A)

/--
**The Cauchy–Davenport Theorem (Single Sumset over $\mathbb{Z}/p\mathbb{Z}$)**:
For any prime $p$ and non-empty subsets $A, B \subseteq \mathbb{Z}/p\mathbb{Z}$:
$$|A + B| \ge \min(p, |A| + |B| - 1)$$
-/
theorem cauchy_davenport {p : ℕ} (hp : Nat.Prime p)
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card := by
  sorry

/--
**Cauchy–Davenport on Integers**:
For non-empty finite subsets $A, B \subseteq \mathbb{Z}$, $|A + B| \ge |A| + |B| - 1$.
-/
theorem cauchy_davenport_integers (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  sorry

/--
**Cardinality Conservation of the Dyson $e$-Transform**:
$$|A'| + |B'| = |A| + |B|$$
-/
theorem dysonTransform_card [AddCommGroup G] (e : G) (A B : Finset G) :
    (dysonTransformFst e A B).card + (dysonTransformSnd e A B).card = A.card + B.card := by
  sorry

/--
**Sumset Size Contraction under the Dyson $e$-Transform**:
$$|A' + B'| \le |A + B|$$
-/
theorem dysonTransform_sumset_card_le [AddCommGroup G] (e : G) (A B : Finset G) :
    (dysonTransformFst e A B + dysonTransformSnd e A B).card ≤ (A + B).card := by
  sorry

/--
**The Iterated Cauchy–Davenport Theorem**:
For any prime $p$, integer $k \ge 1$, and non-empty subsets $A_1, \dots, A_k \subseteq \mathbb{Z}/p\mathbb{Z}$:
$$\left| \sum_{i=1}^k A_i \right| \ge \min\left(p, \sum_{i=1}^k |A_i| - k + 1\right)$$
-/
theorem cauchy_davenport_iterated {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : 1 ≤ k)
    (As : Fin k → Finset (ZMod p)) (h_nonempty : ∀ i, (As i).Nonempty) :
    min p ((∑ i : Fin k, (As i).card) - k + 1) ≤
      (∑ i : Fin k, As i).card := by
  sorry

/--
**Full Group Surjectivity**:
If the sum of cardinalities satisfies $\sum_{i=1}^k |A_i| \ge p + k - 1$,
then the iterated sumset $\sum_{i=1}^k A_i$ equals the entire group $\mathbb{Z}/p\mathbb{Z}$.
-/
theorem iterated_sumset_eq_univ_of_card_ge {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : 1 ≤ k)
    (As : Fin k → Finset (ZMod p)) (h_nonempty : ∀ i, (As i).Nonempty)
    (h_sum : p + k - 1 ≤ ∑ i : Fin k, (As i).card) :
    (∑ i : Fin k, As i).card = p := by
  sorry

/--
**Multiple Self-Sumset Bound ($k A$)**:
For any $k \ge 1$ and non-empty subset $A \subseteq \mathbb{Z}/p\mathbb{Z}$:
$$|k A| \ge \min(p, k |A| - k + 1)$$
-/
theorem cauchy_davenport_self_iterated {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : 1 ≤ k)
    (A : Finset (ZMod p)) (hA : A.Nonempty) :
    min p (k * A.card - k + 1) ≤ (∑ i : Fin k, A).card := by
  sorry

/--
**Iterated Cauchy–Davenport Full Span for EGZ**:
Given $p - 1$ non-zero differences $d_0, \dots, d_{p-2} \in \mathbb{Z}/p\mathbb{Z}$,
the sum of the 2-element sets $A_i = \{0, d_i\}$ spans the whole of $\mathbb{Z}/p\mathbb{Z}$.
-/
theorem egz_cauchy_davenport_span {p : ℕ} (hp : Nat.Prime p)
    (d : Fin (p - 1) → ZMod p) (hd : ∀ i, d i ≠ 0) :
    (∑ i : Fin (p - 1), ({0, d i} : Finset (ZMod p))).card = p := by
  sorry

/--
**Identical Elements Case**:
$p$ copies of any element $x \in \mathbb{Z}/p\mathbb{Z}$ sum to $0$.
-/
theorem egz_identical_sum_zero {p : ℕ} (hp : Nat.Prime p) (x : ZMod p) :
    (∑ i : Fin p, x) = 0 := by
  sorry

end CauchyDavenport
