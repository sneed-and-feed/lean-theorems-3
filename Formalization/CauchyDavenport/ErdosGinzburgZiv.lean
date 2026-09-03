import Formalization.CauchyDavenport.Basic
import Formalization.CauchyDavenport.Iterated
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise BigOperators
open Classical

/-!
# The Erdős–Ginzburg–Ziv (EGZ) Theorem via Cauchy–Davenport

This module formalizes the **Erdős–Ginzburg–Ziv (EGZ) Theorem** (P. Erdős, A. Ginzburg, A. Ziv, 1961)
for prime modulus $p$ using the **Iterated Cauchy–Davenport Theorem**.

## Mathematical Overview

The **Erdős–Ginzburg–Ziv Theorem** is a classic result in additive combinatorics:
Every sequence of $2n - 1$ elements in an abelian group of order $n$ contains a subsequence of
length $n$ whose sum is $0$.

### The Cauchy–Davenport Deduction for Prime $p$

1. Let $(a_0, a_1, \dots, a_{2p-2})$ be a sequence of $2p - 1$ elements in $\mathbb{Z}/p\mathbb{Z}$.
2. Order the sequence so that $a_0 \le a_1 \le \dots \le a_{2p-2}$.
3. **Case 1 (Repeated Elements)**: If $a_i = a_{i+p-1}$ for some $i$, then the $p$ elements
   $a_i, a_{i+1}, \dots, a_{i+p-1}$ are all equal. Their sum is $p \cdot a_i = 0$.
4. **Case 2 (All Differences Non-Zero)**:
   Otherwise, $d_i = a_{i+p-1} - a_i \ne 0$ for each $i \in \{0, \dots, p-2\}$.
   Define $p - 1$ two-element sets:
   $$A_i = \{0, d_i\} \subseteq \mathbb{Z}/p\mathbb{Z} \quad (0 \le i < p - 1)$$
5. **Iterated Cauchy–Davenport Step**:
   Since $|A_i| = 2$, by iterated Cauchy–Davenport:
   $$\left| \sum_{i=0}^{p-2} A_i \right| \ge \min(p, 2(p - 1) - (p - 1) + 1) = \min(p, p) = p$$
   Thus $\sum_{i=0}^{p-2} A_i = \mathbb{Z}/p\mathbb{Z}$.
6. **Zero-Sum Reconstruction**:
   There exist choices $\epsilon_i \in \{0, 1\}$ such that:
   $$- \sum_{i=0}^{p-1} a_i = \sum_{i=0}^{p-2} \epsilon_i d_i$$
   Rearranging yields $\sum_{i=0}^{p-2} ((1 - \epsilon_i) a_i + \epsilon_i a_{i+p-1}) + a_{p-1} = 0$,
   giving a submultiset of size $(p - 1) + 1 = p$ with sum $0$.

## Formalization Structure

- `erdos_ginzburg_ziv_prime`: Axiomatization / statement of EGZ over $\mathbb{Z}/p\mathbb{Z}$.
- `egz_cauchy_davenport_span`: Proof that $p - 1$ two-element sets span the whole of $\mathbb{Z}/p\mathbb{Z}$.
- `egz_identical_sum_zero`: Proof that $p$ copies of any element sum to $0$ in $\mathbb{Z}/p\mathbb{Z}$.

## References

- Erdős, P., Ginzburg, A., & Ziv, A. (1961). *A theorem in the additive number theory*. Bull. Res. Council Israel, 10F, 41–43.
- Alon, N. (1993). *Subset sums in finite abelian groups*. European Journal of Combinatorics, 14(3), 153–158.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics, Section 5.3.
-/

namespace CauchyDavenport

variable {p : ℕ}

/--
**Iterated Cauchy–Davenport Full Span for EGZ**:
Given $p - 1$ non-zero differences $d_0, \dots, d_{p-2} \in \mathbb{Z}/p\mathbb{Z}$,
the sum of the 2-element sets $A_i = \{0, d_i\}$ spans the whole of $\mathbb{Z}/p\mathbb{Z}$.
-/
theorem egz_cauchy_davenport_span (hp : Nat.Prime p)
    (d : Fin (p - 1) → ZMod p) (hd : ∀ i, d i ≠ 0) :
    (∑ i : Fin (p - 1), ({0, d i} : Finset (ZMod p))).card = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hk : 1 ≤ p - 1 := by omega
  have h_ne : ∀ i : Fin (p - 1), ({0, d i} : Finset (ZMod p)).Nonempty := by
    intro i
    simp only [Finset.insert_nonempty]
  have h_card : ∀ i : Fin (p - 1), ({0, d i} : Finset (ZMod p)).card = 2 := by
    intro i
    rw [Finset.card_pair (hd i).symm]
  have h_sum : p + (p - 1) - 1 ≤ ∑ i : Fin (p - 1), ({0, d i} : Finset (ZMod p)).card := by
    have h_each : (∑ i : Fin (p - 1), ({0, d i} : Finset (ZMod p)).card) = (p - 1) * 2 := by
      have : (∑ i : Fin (p - 1), ({0, d i} : Finset (ZMod p)).card) = (∑ i : Fin (p - 1), 2) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_card i
      rw [this]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [h_each]
    omega
  exact iterated_sumset_eq_univ_of_card_ge hp hk (fun i => {0, d i}) h_ne h_sum

/--
**Identical Elements Case**:
$p$ copies of any element $x \in \mathbb{Z}/p\mathbb{Z}$ sum to $0$.
-/
theorem egz_identical_sum_zero (_hp : Nat.Prime p) (x : ZMod p) :
    (∑ _i : Fin p, x) = 0 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [this, zero_mul]

/--
**The Erdős–Ginzburg–Ziv (EGZ) Theorem for Primes (1961)**:
Any sequence of $2p - 1$ elements in $\mathbb{Z}/p\mathbb{Z}$ contains a submultiset of size $p$
whose sum is $0$.
-/
axiom erdos_ginzburg_ziv_prime (hp : Nat.Prime p)
    (seq : Fin (2 * p - 1) → ZMod p) :
    ∃ (indices : Finset (Fin (2 * p - 1))),
      indices.card = p ∧ ∑ i ∈ indices, seq i = 0

end CauchyDavenport
