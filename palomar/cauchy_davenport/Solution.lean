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
set_option linter.style.haveILetI false

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
    min p (A.card + B.card - 1) ≤ (A + B).card :=
  ZMod.cauchy_davenport hp hA hB

/--
**Cauchy–Davenport in Torsion-Free Groups**:
In any torsion-free additive group (such as $\mathbb{Z}$), $|A + B| \ge |A| + |B| - 1$.
-/
theorem cauchy_davenport_of_isAddTorsionFree [AddGroup G] [IsAddTorsionFree G]
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card :=
  _root_.cauchy_davenport_of_isAddTorsionFree hA hB

/--
**Cauchy–Davenport on Integers**:
For non-empty finite subsets $A, B \subseteq \mathbb{Z}$, $|A + B| \ge |A| + |B| - 1$.
-/
theorem cauchy_davenport_integers (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card :=
  cauchy_davenport_of_isAddTorsionFree hA hB

/--
**Cardinality Conservation of the Dyson $e$-Transform**:
$$|A'| + |B'| = |A| + |B|$$
-/
theorem dysonTransform_card [AddCommGroup G] (e : G) (A B : Finset G) :
    (dysonTransformFst e A B).card + (dysonTransformSnd e A B).card = A.card + B.card := by
  have h := Finset.addDysonETransform.card e (A, B)
  exact h

/--
**Sumset Inclusion of the Dyson $e$-Transform**:
$$A' + B' \subseteq A + B$$
-/
theorem dysonTransform_sumset_subset [AddCommGroup G] (e : G) (A B : Finset G) :
    dysonTransformFst e A B + dysonTransformSnd e A B ⊆ A + B := by
  have h := Finset.addDysonETransform.subset e (A, B)
  exact h

/--
**Sumset Size Contraction under the Dyson $e$-Transform**:
$$|A' + B'| \le |A + B|$$
-/
theorem dysonTransform_sumset_card_le [AddCommGroup G] (e : G) (A B : Finset G) :
    (dysonTransformFst e A B + dysonTransformSnd e A B).card ≤ (A + B).card :=
  Finset.card_le_card (dysonTransform_sumset_subset e A B)

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

/--
**Iterated Cauchy–Davenport Full Span for EGZ**:
Given $p - 1$ non-zero differences $d_0, \dots, d_{p-2} \in \mathbb{Z}/p\mathbb{Z}$,
the sum of the 2-element sets $A_i = \{0, d_i\}$ spans the whole of $\mathbb{Z}/p\mathbb{Z}$.
-/
theorem egz_cauchy_davenport_span {p : ℕ} (hp : Nat.Prime p)
    (d : Fin (p - 1) → ZMod p) (hd : ∀ i, d i ≠ 0) :
    (∑ i : Fin (p - 1), ({0, d i} : Finset (ZMod p))).card = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
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
theorem egz_identical_sum_zero {p : ℕ} (hp : Nat.Prime p) (x : ZMod p) :
    (∑ i : Fin p, x) = 0 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [this, zero_mul]

end CauchyDavenport
