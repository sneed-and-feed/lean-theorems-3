import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.ETransform
import Mathlib.GroupTheory.Order.Min
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise
open Classical

/-!
# The Cauchy–Davenport Theorem: Foundations and e-Transforms

This module formalizes the foundational single-step **Cauchy–Davenport Theorem** (Cauchy 1813,
Davenport 1935) and Davenport's Dyson $e$-transform techniques in additive combinatorics.

## Mathematical Overview

Let $G$ be an additive group and let $A, B \subseteq G$ be non-empty finite subsets.
1. **Prime Cyclic Groups $\mathbb{Z}/p\mathbb{Z}$**:
   $$|A + B| \ge \min(p, |A| + |B| - 1)$$
2. **Torsion-Free Groups (e.g. $\mathbb{Z}$)**:
   $$|A + B| \ge |A| + |B| - 1$$
3. **General Groups with Minimal Subgroup Order**:
   $$|A + B| \ge \min(\mathrm{minOrder}(G), |A| + |B| - 1)$$
4. **Davenport's Dyson $e$-transform**:
   For any shift element $e \in G$, the pair $(A, B)$ is mapped to:
   $$A' = A \cup (e +ᵥ B), \quad B' = B \cap (-e +ᵥ A)$$
   This preserves the sum of cardinalities:
   $$|A'| + |B'| = |A| + |B|$$
   while contracting the sumset:
   $$A' + B' \subseteq A + B \implies |A' + B'| \le |A + B|$$

## References

- Cauchy, A.-L. (1813). *Recherches sur les nombres*. Journal de l'École Polytechnique, 9, 99–123.
- Davenport, H. (1935). *On the addition of residue classes*. Journal of the London Mathematical Society, 10, 30–32.
- DeVos, M. (2009). *On a generalization of the Cauchy-Davenport theorem*.
-/

namespace CauchyDavenport

variable {G : Type*} [DecidableEq G]

section GroupBounds

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
**Cauchy–Davenport for Linearly Ordered Additive Cancellative Semigroups**:
In any linearly ordered cancellative structure, $|A + B| \ge |A| + |B| - 1$.
-/
theorem cauchy_davenport_ordered {α : Type*} [LinearOrder α] [Add α]
    [IsCancelAdd α] [AddLeftMono α] [AddRightMono α]
    (A B : Finset α) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card :=
  cauchy_davenport_add_of_linearOrder_isCancelAdd hA hB

/--
**General Group Cauchy–Davenport Bound**:
For any additive group $G$ and non-empty subsets $A, B \subseteq G$:
$$|A + B| \ge \min(\mathrm{minOrder}(G), |A| + |B| - 1)$$
-/
theorem cauchy_davenport_minOrder [AddGroup G] (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min (AddMonoid.minOrder G) ↑(A.card + B.card - 1) ≤ (A + B).card :=
  cauchy_davenport_minOrder_add hA hB

end GroupBounds

section DysonETransform

variable [AddCommGroup G]

/--
**Davenport's Dyson $e$-transform**:
Given a pair of finite sets $(A, B)$ in an additive group $G$ and a shift $e \in G$,
the Dyson transform produces the pair $(A \cup (e +ᵥ B), B \cap (-e +ᵥ A))$.
-/
def dysonTransform (e : G) (pair : Finset G × Finset G) : Finset G × Finset G :=
  Finset.addDysonETransform e pair

/-- The first component of the Dyson transform: $A' = A \cup (e +ᵥ B)$. -/
def dysonTransformFst (e : G) (A B : Finset G) : Finset G :=
  A ∪ (e +ᵥ B)

/-- The second component of the Dyson transform: $B' = B \cap (-e +ᵥ A)$. -/
def dysonTransformSnd (e : G) (A B : Finset G) : Finset G :=
  B ∩ (-e +ᵥ A)

@[simp]
theorem dysonTransform_fst (e : G) (A B : Finset G) :
    (dysonTransform e (A, B)).1 = dysonTransformFst e A B :=
  rfl

@[simp]
theorem dysonTransform_snd (e : G) (A B : Finset G) :
    (dysonTransform e (A, B)).2 = dysonTransformSnd e A B :=
  rfl

/--
**Cardinality Conservation of the Dyson $e$-Transform**:
$$|A'| + |B'| = |A| + |B|$$
-/
theorem dysonTransform_card (e : G) (A B : Finset G) :
    (dysonTransformFst e A B).card + (dysonTransformSnd e A B).card = A.card + B.card := by
  have h := Finset.addDysonETransform.card e (A, B)
  exact h

/--
**Sumset Inclusion of the Dyson $e$-Transform**:
$$A' + B' \subseteq A + B$$
-/
theorem dysonTransform_sumset_subset (e : G) (A B : Finset G) :
    dysonTransformFst e A B + dysonTransformSnd e A B ⊆ A + B := by
  have h := Finset.addDysonETransform.subset e (A, B)
  exact h

/--
**Sumset Size Contraction under the Dyson $e$-Transform**:
$$|A' + B'| \le |A + B|$$
-/
theorem dysonTransform_sumset_card_le (e : G) (A B : Finset G) :
    (dysonTransformFst e A B + dysonTransformSnd e A B).card ≤ (A + B).card :=
  Finset.card_le_card (dysonTransform_sumset_subset e A B)

/-- The Dyson transform is idempotent: applied twice with the same $e$, it stabilizes. -/
theorem dysonTransform_idem (e : G) (A B : Finset G) :
    dysonTransform e (dysonTransform e (A, B)) = dysonTransform e (A, B) :=
  Finset.addDysonETransform_idem e (A, B)

/-- Subsetting property: $e +ᵥ B' \subseteq A'$. -/
theorem dysonTransform_smul_snd_subset_fst (e : G) (A B : Finset G) :
    e +ᵥ dysonTransformSnd e A B ⊆ dysonTransformFst e A B := by
  intro x hx
  simp only [dysonTransformFst, dysonTransformSnd, Finset.mem_vadd_finset, Finset.mem_inter,
    Finset.mem_union] at hx ⊢
  obtain ⟨y, ⟨hyB, ⟨z, hzA, rfl⟩⟩, rfl⟩ := hx
  left
  simpa using hzA

end DysonETransform

section ElementaryBounds

variable [AddGroup G]

/-- Translation of a finset by a singleton is the image under the shift map. -/
theorem add_singleton_eq_image (A : Finset G) (b : G) :
    A + {b} = A.image (fun a => a + b) := by
  ext x
  simp only [Finset.mem_add, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, b', rfl, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, b, rfl, rfl⟩

/-- Adding a singleton to $A$ preserves cardinality: $|A + \{b\}| = |A|$. -/
theorem card_add_singleton (A : Finset G) (b : G) :
    (A + {b}).card = A.card := by
  rw [add_singleton_eq_image]
  exact Finset.card_image_of_injective _ (fun x y h => add_right_cancel h)

/-- Left singleton sum is the image under left shift. -/
theorem singleton_add_eq_image (a : G) (B : Finset G) :
    {a} + B = B.image (fun b => a + b) := by
  ext x
  simp only [Finset.mem_add, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨a', rfl, b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨a, rfl, b, hb, rfl⟩

/-- Adding a singleton on the left preserves cardinality: $|\{a\} + B| = |B|$. -/
theorem card_singleton_add (a : G) (B : Finset G) :
    ({a} + B).card = B.card := by
  rw [singleton_add_eq_image]
  exact Finset.card_image_of_injective _ (fun x y h => add_left_cancel h)

/-- Lower bound: $|A| \le |A + B|$ for non-empty $B$. -/
theorem card_le_card_add_left (A : Finset G) {B : Finset G} (hB : B.Nonempty) :
    A.card ≤ (A + B).card := by
  obtain ⟨b, hb⟩ := hB
  have h_sub : A + {b} ⊆ A + B := by
    rw [add_singleton_eq_image]
    intro x hx
    simp only [Finset.mem_image, Finset.mem_add] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, b, hb, rfl⟩
  have h_card := Finset.card_le_card h_sub
  rwa [card_add_singleton] at h_card

/-- Lower bound: $|B| \le |A + B|$ for non-empty $A$. -/
theorem card_le_card_add_right {A : Finset G} (hA : A.Nonempty) (B : Finset G) :
    B.card ≤ (A + B).card := by
  obtain ⟨a, ha⟩ := hA
  have h_sub : {a} + B ⊆ A + B := by
    rw [singleton_add_eq_image]
    intro x hx
    simp only [Finset.mem_image, Finset.mem_add] at hx ⊢
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨a, ha, b, hb, rfl⟩
  have h_card := Finset.card_le_card h_sub
  rwa [card_singleton_add] at h_card

end ElementaryBounds

end CauchyDavenport
