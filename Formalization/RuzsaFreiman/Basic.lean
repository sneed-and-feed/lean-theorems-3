import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Pointwise

set_option linter.unusedSectionVars false

/-!
# Foundational Sumset Operations & Doubling Constants

This module formalizes the elementary operations of additive combinatorics:
sumsets, difference sets, and doubling constants in arbitrary groups.

## Mathematical Overview

Let $G$ be an additive group (such as $\mathbb{Z}$, $\mathbb{Z}/N\mathbb{Z}$, or $\mathbb{F}_p^n$).
For any two finite subsets $A, B \subseteq G$:
1. The **sumset** is $A + B = \{a + b : a \in A, b \in B\}$.
2. The **difference set** is $A - B = \{a - b : a \in A, b \in B\}$.
3. The **doubling constant** is $\sigma(A) = \frac{|A + A|}{|A|}$.
4. The **difference constant** is $\delta(A) = \frac{|A - A|}{|A|}$.

In general, for $A, B$ non-empty:
- Trivial lower bounds: $|A + B| \ge |A|$ and $|A + B| \ge |B|$.
- In torsion-free groups (e.g. $\mathbb{Z}$), $|A + B| \ge |A| + |B| - 1$, with equality
  if and only if $A$ and $B$ are arithmetic progressions with the same common difference.

## Formalization Structure

- `sumset`: The Minkowski sum $A + B$.
- `diffset`: The Minkowski difference $A - B$.
- `doublingConstant`: The ratio $|A + A| / |A|$ as a non-negative rational number.
- `differenceConstant`: The ratio $|A - A| / |A|$.
- `add_singleton_eq_image`: Translation by a singleton is the image under translation.
- `card_add_singleton`: Cardinality invariance under translation $|A + \{b\}| = |A|$.
- `card_le_card_add_left`: Proof that $|A + B| \ge |A|$ for $B$ non-empty.
- `card_le_card_add_right`: Proof that $|A + B| \ge |B|$ for $A$ non-empty.
- `doublingConstant_ge_one`: Doubling constant is always $\ge 1$ for non-empty sets.
- `iteratedSumset`: $k A = A + \dots + A$ ($k$ terms).

## References

- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics.
- Nathanson, M. B. (1996). *Additive Number Theory: Inverse Problems and the Geometry of Sumsets*. Springer GTM 165.
-/

namespace RuzsaFreiman

variable {G : Type*} [DecidableEq G] [AddGroup G]

/-- The sumset $A + B = \{a + b : a \in A, b \in B\}$. -/
def sumset (A B : Finset G) : Finset G := A + B

/-- The difference set $A - B = \{a - b : a \in A, b \in B\}$. -/
def diffset (A B : Finset G) : Finset G := A - B

/-- The doubling constant $\sigma(A) = \frac{|A + A|}{|A|}$. -/
def doublingConstant (A : Finset G) : ℚ :=
  (A + A).card / (A.card : ℚ)

/-- The difference constant $\delta(A) = \frac{|A - A|}{|A|}$. -/
def differenceConstant (A : Finset G) : ℚ :=
  (A - A).card / (A.card : ℚ)

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

/-- For any $b \in G$, the translation $A + \{b\}$ has cardinality $|A|$. -/
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

/-- For any $a \in G$, the translation $\{a\} + B$ has cardinality $|B|$. -/
theorem card_singleton_add (a : G) (B : Finset G) :
    ({a} + B).card = B.card := by
  rw [singleton_add_eq_image]
  exact Finset.card_image_of_injective _ (fun x y h => add_left_cancel h)

/-- Lower bound: $|A + B| \ge |A|$ for non-empty $B$. -/
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

/-- Lower bound: $|A + B| \ge |B|$ for non-empty $A$. -/
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

/-- Doubling constant is at least 1 for non-empty sets. -/
theorem doublingConstant_ge_one {A : Finset G} (hA : A.Nonempty) :
    1 ≤ doublingConstant A := by
  dsimp [doublingConstant]
  have h_le : A.card ≤ (A + A).card := card_le_card_add_left A hA
  have hpos : (0 : ℚ) < (A.card : ℚ) := by
    exact Nat.cast_pos.mpr hA.card_pos
  rw [le_div_iff₀ hpos]
  simp only [one_mul]
  exact Nat.cast_le.mpr h_le

/-- Iterated sumset $k A = A + \dots + A$ ($k$ terms). -/
def iteratedSumset (k : ℕ) (A : Finset G) : Finset G :=
  match k with
  | 0 => {0}
  | k + 1 => iteratedSumset k A + A

/-- Equivalence between `iteratedSumset` and pointwise `nsmul`. -/
theorem iteratedSumset_eq_nsmul (k : ℕ) (A : Finset G) :
    iteratedSumset k A = k • A := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iteratedSumset, ih, succ_nsmul]

end RuzsaFreiman
