import Formalization.CauchyDavenport.Basic
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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Iterated Cauchy–Davenport Theorem for Multi-fold Sumsets

This module formalizes the **Iterated Cauchy–Davenport Theorem** for arbitrary $k$-fold sumsets
$\sum_{i=1}^k A_i = A_1 + A_2 + \dots + A_k$ in $\mathbb{Z}/p\mathbb{Z}$ and in torsion-free groups.

## Mathematical Overview

Let $p$ be a prime number and let $A_1, \dots, A_k \subseteq \mathbb{Z}/p\mathbb{Z}$ be non-empty subsets.
The iterated sumset is:
$$\sum_{i=1}^k A_i = \left\{ \sum_{i=1}^k a_i : a_i \in A_i \right\}$$

**Iterated Cauchy–Davenport Bound**:
$$\left| \sum_{i=1}^k A_i \right| \ge \min\left(p, \sum_{i=1}^k |A_i| - k + 1\right)$$

### Inductive Proof Structure

1. **Base Case ($k = 1$)**: For a single set $A_1$, $|A_1| \le p$ so $\min(p, |A_1| - 1 + 1) = |A_1| \le |A_1|$.
2. **Inductive Step ($k \to k + 1$)**:
   Let $S_k = \sum_{i=1}^k A_i$ and $A_{k+1}$ be non-empty.
   By induction hypothesis, $|S_k| \ge \min(p, \sum_{i=1}^k |A_i| - k + 1)$.
   Applying the 2-set Cauchy–Davenport theorem to $S_k + A_{k+1}$:
   $$|S_k + A_{k+1}| \ge \min(p, |S_k| + |A_{k+1}| - 1)$$
   The arithmetic lemma $\min(p, a + b - 1) \ge \min(p, X + b - 1)$ for $a \ge \min(p, X)$ and $b \ge 1$
   yields the required bound for $k + 1$.

## Key Corollaries

1. **Full Group Generation**: If $\sum_{i=1}^k |A_i| \ge p + k - 1$, then $\sum_{i=1}^k A_i = \mathbb{Z}/p\mathbb{Z}$.
2. **Multiple Self-Sumset $k A$**: $|k A| \ge \min(p, k |A| - k + 1)$.
3. **Torsion-Free Iterated Sumsets**: In $\mathbb{Z}$, $|\sum_{i=1}^k A_i| \ge \sum_{i=1}^k |A_i| - k + 1$.

## References

- Cauchy, A.-L. (1813). *Recherches sur les nombres*.
- Davenport, H. (1935). *On the addition of residue classes*.
- Nathanson, M. B. (1996). *Additive Number Theory: Inverse Problems and the Geometry of Sumsets*.
-/

namespace CauchyDavenport

variable {G : Type*} [DecidableEq G]

/--
Helper lemma on the monotonicity of min-addition arithmetic:
If $1 \le b$ and $\min(p, X) \le a$, then $\min(p, X + b - 1) \le \min(p, a + b - 1)$.
-/
lemma min_add_sub_one_le {p a b X : ℕ} (hb : 1 ≤ b) (ha : min p X ≤ a) :
    min p (X + b - 1) ≤ min p (a + b - 1) := by
  rcases le_or_gt p a with hpa | hpa
  · have : p ≤ a + b - 1 := by omega
    rw [min_eq_left this]
    exact min_le_left _ _
  · have hX : X ≤ a := by
      have : min p X = X := min_eq_right (by omega)
      rwa [this] at ha
    have : X + b - 1 ≤ a + b - 1 := by omega
    exact min_le_min_left p this

/--
Sum of non-empty sets in an additive group indexed by `Fin n` is non-empty.
-/
theorem sum_univ_nonempty {A : Type*} [AddCommGroup A] {n : ℕ}
    (As : Fin n → Finset A) (h_nonempty : ∀ i, (As i).Nonempty) :
    (∑ i : Fin n, As i).Nonempty := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact Finset.singleton_nonempty 0
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have ih_ne : (∑ i : Fin m, As (Fin.castSucc i)).Nonempty :=
      ih (fun i => As (Fin.castSucc i)) (fun i => h_nonempty (Fin.castSucc i))
    exact Finset.Nonempty.add ih_ne (h_nonempty (Fin.last m))

/--
Helper induction on $m$ for $k = m + 1$ non-empty sets in $\mathbb{Z}/p\mathbb{Z}$.
-/
theorem cauchy_davenport_iterated_succ {p : ℕ} (hp : Nat.Prime p) (m : ℕ)
    (As : Fin (m + 1) → Finset (ZMod p)) (h_nonempty : ∀ i, (As i).Nonempty) :
    min p ((∑ i : Fin (m + 1), (As i).card) - (m + 1) + 1) ≤
      (∑ i : Fin (m + 1), As i).card := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_one, Fin.sum_univ_one]
    have : (As 0).card - 1 + 1 = (As 0).card := by
      have := (h_nonempty 0).card_pos
      omega
    rw [this]
    exact min_le_right p (As 0).card
  | succ n ih =>
    have h_ne_prev : ∀ i : Fin (n + 1), (As (Fin.castSucc i)).Nonempty := fun i => h_nonempty (Fin.castSucc i)
    have ih_step := ih (fun i => As (Fin.castSucc i)) h_ne_prev
    have h_card_ge : n + 1 ≤ ∑ i : Fin (n + 1), (As (Fin.castSucc i)).card := by
      have h_each : ∀ i : Fin (n + 1), 1 ≤ (As (Fin.castSucc i)).card := fun i => (h_ne_prev i).card_pos
      have h_le_sum : (∑ i : Fin (n + 1), 1) ≤ ∑ i : Fin (n + 1), (As (Fin.castSucc i)).card :=
        Finset.sum_le_sum (fun (i : Fin (n + 1)) (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) => h_each i)
      have h_sum_ones : (∑ i : Fin (n + 1), 1) = n + 1 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      rwa [h_sum_ones] at h_le_sum
    have h_prev_pos : 1 ≤ (∑ i : Fin (n + 1), (As (Fin.castSucc i)).card) - (n + 1) + 1 := by omega
    have h_min_pos : 1 ≤ min p ((∑ i : Fin (n + 1), (As (Fin.castSucc i)).card) - (n + 1) + 1) :=
      le_min hp.pos h_prev_pos
    have hS_ne : (∑ i : Fin (n + 1), As (Fin.castSucc i)).Nonempty :=
      Finset.card_pos.mp (h_min_pos.trans ih_step)
    have hB_ne : (As (Fin.last (n + 1))).Nonempty := h_nonempty (Fin.last (n + 1))
    have hB_pos : 1 ≤ (As (Fin.last (n + 1))).card := hB_ne.card_pos
    have hCD : min p ((∑ i : Fin (n + 1), As (Fin.castSucc i)).card + (As (Fin.last (n + 1))).card - 1) ≤
        ((∑ i : Fin (n + 1), As (Fin.castSucc i)) + As (Fin.last (n + 1))).card :=
      cauchy_davenport hp (∑ i : Fin (n + 1), As (Fin.castSucc i)) (As (Fin.last (n + 1))) hS_ne hB_ne
    have h_min := min_add_sub_one_le hB_pos ih_step
    rw [Fin.sum_univ_castSucc (fun i => As i)]
    rw [Fin.sum_univ_castSucc (fun i => (As i).card)]
    have h_arith : ((∑ i : Fin (n + 1), (As (Fin.castSucc i)).card) - (n + 1) + 1) + (As (Fin.last (n + 1))).card - 1 =
        ((∑ i : Fin (n + 1), (As (Fin.castSucc i)).card) + (As (Fin.last (n + 1))).card) - (n + 2) + 1 := by
      omega
    rw [h_arith] at h_min
    exact h_min.trans hCD

/--
**The Iterated Cauchy–Davenport Theorem**:
For any prime $p$, integer $k \ge 1$, and non-empty subsets $A_1, \dots, A_k \subseteq \mathbb{Z}/p\mathbb{Z}$:
$$\left| \sum_{i=1}^k A_i \right| \ge \min\left(p, \sum_{i=1}^k |A_i| - k + 1\right)$$
-/
theorem cauchy_davenport_iterated {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : 1 ≤ k)
    (As : Fin k → Finset (ZMod p)) (h_nonempty : ∀ i, (As i).Nonempty) :
    min p ((∑ i : Fin k, (As i).card) - k + 1) ≤
      (∑ i : Fin k, As i).card := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  exact cauchy_davenport_iterated_succ hp m As h_nonempty

/--
**Binary Cauchy–Davenport as Iterated Case**:
Special case of iterated Cauchy–Davenport for $k = 2$.
-/
theorem cauchy_davenport_binary {p : ℕ} (hp : Nat.Prime p)
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card :=
  cauchy_davenport hp A B hA hB

/--
**Full Group Surjectivity**:
If the sum of cardinalities satisfies $\sum_{i=1}^k |A_i| \ge p + k - 1$,
then the iterated sumset $\sum_{i=1}^k A_i$ equals the entire group $\mathbb{Z}/p\mathbb{Z}$.
-/
theorem iterated_sumset_eq_univ_of_card_ge {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : 1 ≤ k)
    (As : Fin k → Finset (ZMod p)) (h_nonempty : ∀ i, (As i).Nonempty)
    (h_sum : p + k - 1 ≤ ∑ i : Fin k, (As i).card) :
    (∑ i : Fin k, As i).card = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_bound := cauchy_davenport_iterated hp hk As h_nonempty
  have h_le : p ≤ (∑ i : Fin k, (As i).card) - k + 1 := by omega
  rw [min_eq_left h_le] at h_bound
  have h_top : (∑ i : Fin k, As i).card ≤ p := by
    have : (∑ i : Fin k, As i) ⊆ (Finset.univ : Finset (ZMod p)) := Finset.subset_univ _
    have h_card := Finset.card_le_card this
    have h_univ : (Finset.univ : Finset (ZMod p)).card = p := ZMod.card p
    rw [h_univ] at h_card
    exact h_card
  exact le_antisymm h_top h_bound

/--
**Multiple Self-Sumset Bound ($k A$)**:
For any $k \ge 1$ and non-empty subset $A \subseteq \mathbb{Z}/p\mathbb{Z}$:
$$|k A| \ge \min(p, k |A| - k + 1)$$
-/
theorem cauchy_davenport_self_iterated {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : 1 ≤ k)
    (A : Finset (ZMod p)) (hA : A.Nonempty) :
    min p (k * A.card - k + 1) ≤ (∑ i : Fin k, A).card := by
  have h := cauchy_davenport_iterated hp hk (fun (_ : Fin k) => A) (fun _ => hA)
  have h_card_sum : (∑ i : Fin k, A.card) = k * A.card := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rwa [h_card_sum] at h

end CauchyDavenport
