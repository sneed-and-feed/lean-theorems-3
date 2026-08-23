import Formalization.CauchyDavenport.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Chowla's Generalization to Composite Moduli

This module formalizes **Chowla's Theorem** (I. Chowla, 1935), which generalizes the Cauchy–Davenport
bound to composite moduli $\mathbb{Z}/n\mathbb{Z}$ under coprime generator conditions.

## Mathematical Overview

For composite $n \in \mathbb{N}$, the naive Cauchy–Davenport bound $|A + B| \ge \min(n, |A| + |B| - 1)$
fails in general due to non-trivial subgroup obstruction.
For instance, if $H = \langle d \rangle < \mathbb{Z}/n\mathbb{Z}$ is a proper subgroup with $d \mid n$ ($1 < d < n$),
taking $A = H$ and $B = \{0, d\} \subseteq H$ yields $A + B = H$, so $|A + B| = |H| < |H| + 2 - 1 = |H| + 1$.

**Chowla's Theorem (1935)**:
Let $n \ge 2$. Let $A, B \subseteq \mathbb{Z}/n\mathbb{Z}$ such that:
1. $A$ is non-empty,
2. $0 \in B$,
3. Every non-zero element $b \in B \setminus \{0\}$ is coprime to $n$ ($\gcd(b, n) = 1$).
Then:
$$|A + B| \ge \min(n, |A| + |B| - 1)$$

### Connection to Kneser's Theorem (1953)

Martin Kneser's structural theorem provides the modern perspective:
For any finite abelian group $G$ and subsets $A, B \subseteq G$:
$$|A + B| \ge |A + H| + |B + H| - |H|$$
where $H = \mathrm{Stab}(A + B) = \{g \in G : g + (A + B) = A + B\}$.
If $B \setminus \{0\} \subseteq (\mathbb{Z}/n\mathbb{Z})^\times$, any non-zero element of $H$ would generate the whole group,
so if $A + B \subsetneq \mathbb{Z}/n\mathbb{Z}$, the stabilizer $H$ must be trivial ($|H| = 1$), recovering $|A + B| \ge |A| + |B| - 1$.

## Formalization Structure

- `chowla_theorem`: Axiomatization of Chowla's composite modulus theorem.
- `chowla_singleton`: Base case $|B| = 1$ verified directly.
- `chowla_full_A`: Case $|A| = n$ verified directly.
- `chowla_of_prime`: Recovery of prime Cauchy–Davenport from Chowla's theorem.
- `card_add_coprime_pair_ge`: Cardinality strictly increasing under addition of coprime elements $\{0, b\}$.

## References

- Chowla, I. (1935). *A theorem on the addition of residue classes*. Proc. Indian Acad. Sci., 2, 242–243.
- Kneser, M. (1953). *Abschätzungen der asymptotischen Dichte von Summenmengen*. Math. Z., 58, 459–484.
- Nathanson, M. B. (1996). *Additive Number Theory: Inverse Problems and the Geometry of Sumsets*. Section 2.2.
-/

namespace CauchyDavenport

variable {n : ℕ}

/--
**Chowla's Theorem for Composite Moduli (1935)**:
If $A, B \subseteq \mathbb{Z}/n\mathbb{Z}$ with $0 \in B$, $A \ne \emptyset$, and every non-zero
element of $B$ is coprime to $n$, then $|A + B| \ge \min(n, |A| + |B| - 1)$.
-/
axiom chowla_theorem (n : ℕ) (hn : 2 ≤ n) [NeZero n]
    (A B : Finset (ZMod n)) (hA : A.Nonempty) (hB0 : (0 : ZMod n) ∈ B)
    (h_coprime : ∀ b ∈ B, b ≠ 0 → Nat.Coprime b.val n) :
    min n (A.card + B.card - 1) ≤ (A + B).card

/--
**Chowla Base Case ($|B| = 1$)**:
When $B = \{0\}$, the Chowla bound $|A + \{0\}| \ge \min(n, |A| + 1 - 1) = |A|$ holds with equality.
-/
theorem chowla_singleton (n : ℕ) [NeZero n]
    (A : Finset (ZMod n)) (hA : A.Nonempty) :
    min n (A.card + 1 - 1) ≤ (A + {0}).card := by
  have : (A + {0}).card = A.card := card_add_singleton A 0
  rw [this, Nat.add_sub_cancel]
  have : A ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.card_le_card this
  have h_univ : (Finset.univ : Finset (ZMod n)).card = n := ZMod.card n
  rw [h_univ] at h
  rw [min_eq_right h]

/--
**Chowla Full Set Case ($|A| = n$)**:
When $A = \mathbb{Z}/n\mathbb{Z}$, the sumset $A + B$ is the entire group.
-/
theorem chowla_full_A (n : ℕ) [NeZero n]
    (A B : Finset (ZMod n)) (hA_card : A.card = n) (hB : B.Nonempty) :
    (A + B).card = n := by
  have hA_univ : A = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [ZMod.card n]
    exact hA_card
  have h_univ : A + B = Finset.univ := by
    rw [hA_univ]
    ext x
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨b, hb⟩ := hB
    simp only [Finset.mem_add]
    exact ⟨x - b, Finset.mem_univ _, b, hb, sub_add_cancel x b⟩
  have h_univ_card : (Finset.univ : Finset (ZMod n)).card = n := ZMod.card n
  rw [h_univ, h_univ_card]

/--
**Prime Modulus Deduction**:
When $n = p$ is prime, every non-zero element of $\mathbb{Z}/p\mathbb{Z}$ is automatically coprime to $p$,
so Chowla's theorem applies to all sets containing $0$.
-/
theorem chowla_of_prime {p : ℕ} (hp : Nat.Prime p)
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (hB0 : (0 : ZMod p) ∈ B) :
    min p (A.card + B.card - 1) ≤ (A + B).card := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply chowla_theorem p hp.two_le A B hA hB0
  intro b hb hb_ne
  have hb_val_pos : 0 < b.val := by
    by_contra h_zero
    have h_val_zero : b.val = 0 := by omega
    have : b = 0 := by
      have h_val : (b.val : ZMod p) = (0 : ZMod p) := by rw [h_val_zero, Nat.cast_zero]
      rwa [ZMod.natCast_zmod_val] at h_val
    exact hb_ne this
  have hb_val_lt : b.val < p := ZMod.val_lt b
  have h_cop := (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hb_val_pos hb_val_lt)
  exact h_cop.symm

/--
**Strict Expansion with Coprime Element**:
Adding a coprime generator pair $\{0, b\}$ strictly increases the cardinality of $A$ unless $A = \mathbb{Z}/n\mathbb{Z}$.
-/
theorem card_add_coprime_pair_ge (n : ℕ) (hn : 2 ≤ n) [NeZero n]
    (A : Finset (ZMod n)) (hA : A.Nonempty) (b : ZMod n) (hb : b ≠ 0)
    (h_coprime : Nat.Coprime b.val n) :
    min n (A.card + 1) ≤ (A + {0, b}).card := by
  have hB0 : (0 : ZMod n) ∈ ({0, b} : Finset (ZMod n)) := by simp
  have h_cop : ∀ x ∈ ({0, b} : Finset (ZMod n)), x ≠ 0 → Nat.Coprime x.val n := by
    intro x hx hx_ne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact False.elim (hx_ne rfl)
    · exact h_coprime
  have h_card_B : ({0, b} : Finset (ZMod n)).card = 2 := by
    rw [Finset.card_pair hb.symm]
  have h_chowla := chowla_theorem n hn A {0, b} hA hB0 h_cop
  rw [h_card_B] at h_chowla
  have : A.card + 2 - 1 = A.card + 1 := by omega
  rwa [this] at h_chowla

end CauchyDavenport
