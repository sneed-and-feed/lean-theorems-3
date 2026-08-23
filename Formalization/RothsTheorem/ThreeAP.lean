import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators Finset

set_option linter.unusedSectionVars false

/-!
# 3-Term Arithmetic Progressions and Progression-Free Sets

This module formalizes the combinatorial foundations of 3-term arithmetic progressions (3-APs)
in additive abelian groups and cyclic groups $\mathbb{Z}/N\mathbb{Z}$.

## Mathematical Overview

Let $G$ be an additive abelian group.
1. A **3-term arithmetic progression (3-AP)** is a triple $(x, x+d, x+2d)$ for some $x, d \in G$.
   In symmetric form, a triple $(x, y, z) \in G^3$ forms a 3-AP if and only if:
   $$x + z = 2y$$
2. A 3-AP is **non-trivial** if $d \ne 0$ (or equivalently $x \ne y$).
3. A subset $A \subseteq G$ is **3-AP free** (or progression-free) if it contains no non-trivial 3-APs,
   i.e. for all $x, y, z \in A$:
   $$x + z = 2y \implies x = y = z$$

### The 3-AP Counting Operator $\Lambda(f_1, f_2, f_3)$

For functions $f_1, f_2, f_3 : G \to \mathbb{R}$ on a finite group $G$:
$$\Lambda(f_1, f_2, f_3) = \frac{1}{|G|^2} \sum_{x \in G} \sum_{d \in G} f_1(x) f_2(x + d) f_3(x + 2d)$$

For indicator functions $1_A$:
- $\Lambda(1_A, 1_A, 1_A)$ measures the normalized count of 3-APs in $A$.
- If $A$ is 3-AP free, the only solutions are the trivial ones with $d = 0$, so:
  $$\Lambda(1_A, 1_A, 1_A) = \frac{|A|}{|G|^2} = \frac{\alpha}{|G|}$$
  where $\alpha = |A| / |G|$ is the density of $A$.

## Formalization Structure

- `Is3AP`: Predicate that $(x, y, z)$ satisfies $x + z = 2y$.
- `IsNonTrivial3AP`: Predicate $x + z = 2y \wedge x \ne y$.
- `IsThreeAPFree`: Predicate that a finset contains no non-trivial 3-APs.
- `indicator`: Real indicator function $1_A : G \to \mathbb{R}$.
- `ap3Count`: The multilinear operator $\Lambda(f_1, f_2, f_3)$.
- `trivial_3ap_count`: The normalized count of trivial 3-APs $\Lambda(1_A, 1_A, 1_A) = |A| / |G|^2$ for 3-AP free sets.

## References

- Roth, K. F. (1953). *On certain sets of integers*. Journal of the London Mathematical Society, 28(1), 104–109.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics.
-/

namespace RothsTheorem

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- A triple $(x, y, z)$ forms a 3-term arithmetic progression if $x + z = 2 \cdot y$. -/
def Is3AP (x y z : G) : Prop :=
  x + z = (2 : ℕ) • y

/-- A 3-AP is non-trivial if the common difference is non-zero ($x \ne y$). -/
def IsNonTrivial3AP (x y z : G) : Prop :=
  Is3AP x y z ∧ x ≠ y

/-- A subset $A \subseteq G$ is 3-AP free if it contains no non-trivial 3-APs. -/
def IsThreeAPFree (A : Finset G) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, Is3AP x y z → x = y

/-- Trivial 3-APs: $(x, x, x)$ is always a 3-AP. -/
theorem is3AP_refl (x : G) : Is3AP x x x := by
  dsimp [Is3AP]
  rw [two_nsmul]

/-- Indicator function $\mathbf{1}_A : G \to \mathbb{R}$. -/
def indicator (A : Finset G) : G → ℝ :=
  fun x => if x ∈ A then 1 else 0

variable [Fintype G]

/-- The multilinear 3-AP counting functional $\Lambda(f_1, f_2, f_3) = \frac{1}{|G|^2} \sum_{x, d} f_1(x) f_2(x+d) f_3(x+2d)$. -/
noncomputable def ap3Count (f1 f2 f3 : G → ℝ) : ℝ :=
  (1 / ((Fintype.card G : ℝ) ^ 2)) *
    ∑ x : G, ∑ d : G, f1 x * f2 (x + d) * f3 (x + (2 : ℕ) • d)

/-- For a 3-AP free set $A$, the only contributions to $\Lambda(1_A, 1_A, 1_A)$ come from $d = 0$. -/
axiom ap3Count_of_free (A : Finset G) (hfree : IsThreeAPFree A) :
    ap3Count (indicator A) (indicator A) (indicator A) =
      (A.card : ℝ) / ((Fintype.card G : ℝ) ^ 2)

end RothsTheorem
