import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators Finset

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

variable {G : Type*}

section AP
variable [AddCommGroup G]

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
theorem is3AP_refl (x : G) : Is3AP x x x := (two_nsmul x).symm

/-- Reflection symmetry: $(x, y, z)$ is a 3-AP iff $(z, y, x)$ is a 3-AP. -/
theorem is3AP_symm (x y z : G) : Is3AP x y z ↔ Is3AP z y x := by
  simp [Is3AP, add_comm]

/-- Standard 3-AP parameterization: $(x, x+d, x+2d)$ is always a 3-AP. -/
theorem is3AP_def_add (x d : G) : Is3AP x (x + d) (x + (2 : ℕ) • d) := by
  simp [Is3AP, two_nsmul, add_assoc, add_left_comm]

/-- Characterization of 3-AP freeness via non-existence of non-trivial 3-APs. -/
theorem isThreeAPFree_iff (A : Finset G) :
    IsThreeAPFree A ↔ ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ¬ IsNonTrivial3AP x y z := by
  simp [IsThreeAPFree, IsNonTrivial3AP, not_and]

end AP

section Indicator
variable [DecidableEq G]

/-- Indicator function $\mathbf{1}_A : G \to \mathbb{R}$. -/
def indicator (A : Finset G) : G → ℝ :=
  fun x => if x ∈ A then 1 else 0

/-- Evaluation of indicator function. -/
theorem indicator_apply (A : Finset G) (x : G) :
    indicator A x = if x ∈ A then 1 else 0 := rfl

/-- Indicator is always non-negative. -/
theorem indicator_nonneg (A : Finset G) (x : G) : 0 ≤ indicator A x := by
  dsimp [indicator]; split_ifs <;> positivity

/-- Indicator is bounded by 1. -/
theorem indicator_le_one (A : Finset G) (x : G) : indicator A x ≤ 1 := by
  dsimp [indicator]; split_ifs <;> norm_num

/-- Indicator takes value 1 on elements of $A$. -/
theorem indicator_of_mem (A : Finset G) {x : G} (hx : x ∈ A) : indicator A x = 1 := by
  simp [indicator, hx]

/-- Indicator takes value 0 outside of $A$. -/
theorem indicator_of_not_mem (A : Finset G) {x : G} (hx : x ∉ A) : indicator A x = 0 := by
  simp [indicator, hx]

/-- Indicator is idempotent under multiplication. -/
theorem indicator_mul_self (A : Finset G) (x : G) : indicator A x * indicator A x = indicator A x := by
  dsimp [indicator]; split_ifs <;> ring

/-- Product of indicators is indicator of intersection. -/
theorem indicator_mul_indicator (A B : Finset G) (x : G) :
    indicator A x * indicator B x = indicator (A ∩ B) x := by
  dsimp [indicator]; split_ifs <;> simp_all

/-- Sum of indicator equals cardinality of the finset. -/
theorem sum_indicator [Fintype G] (A : Finset G) : ∑ x : G, indicator A x = (A.card : ℝ) := by
  simp [indicator]

end Indicator

section Counting
variable [AddCommGroup G]

/-- For 3-AP free set $A$, off-diagonal 3-AP product terms vanish. -/
theorem ap3_term_of_free [DecidableEq G] (A : Finset G) (hfree : IsThreeAPFree A) (x d : G) :
    indicator A x * indicator A (x + d) * indicator A (x + (2 : ℕ) • d) =
      if d = 0 then indicator A x else 0 := by
  by_cases hd : d = 0
  · subst hd; simp only [add_zero, nsmul_zero]; dsimp [indicator]; split_ifs <;> ring
  · dsimp [indicator]
    split_ifs with hx hxd hx2d
    · exact (hd (add_left_cancel (a := x) (by simpa using (hfree x hx (x + d) hxd (x + (2 : ℕ) • d) hx2d (is3AP_def_add x d)).symm))).elim
    all_goals ring

variable [Fintype G]

/-- The multilinear 3-AP counting functional $\Lambda(f_1, f_2, f_3) = \frac{1}{|G|^2} \sum_{x, d} f_1(x) f_2(x+d) f_3(x+2d)$. -/
noncomputable def ap3Count (f1 f2 f3 : G → ℝ) : ℝ :=
  (1 / ((Fintype.card G : ℝ) ^ 2)) *
    ∑ x : G, ∑ d : G, f1 x * f2 (x + d) * f3 (x + (2 : ℕ) • d)

/-- Non-negativity of `ap3Count` for non-negative inputs. -/
theorem ap3Count_nonneg {f1 f2 f3 : G → ℝ}
    (h1 : ∀ x, 0 ≤ f1 x) (h2 : ∀ x, 0 ≤ f2 x) (h3 : ∀ x, 0 ≤ f3 x) :
    0 ≤ ap3Count f1 f2 f3 := by
  dsimp [ap3Count]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun d _ =>
    mul_nonneg (mul_nonneg (h1 x) (h2 _)) (h3 _)

variable [DecidableEq G]

/-- Non-negativity of 3-AP count on indicators. -/
theorem ap3Count_indicator_nonneg (A : Finset G) :
    0 ≤ ap3Count (indicator A) (indicator A) (indicator A) :=
  ap3Count_nonneg (indicator_nonneg A) (indicator_nonneg A) (indicator_nonneg A)

/-- For a 3-AP free set $A$, the only contributions to $\Lambda(1_A, 1_A, 1_A)$ come from $d = 0$. -/
theorem ap3Count_of_free (A : Finset G) (hfree : IsThreeAPFree A) :
    ap3Count (indicator A) (indicator A) (indicator A) =
      (A.card : ℝ) / ((Fintype.card G : ℝ) ^ 2) := by
  dsimp [ap3Count]
  have h_inner x : (∑ d : G, indicator A x * indicator A (x + d) * indicator A (x + (2 : ℕ) • d)) = indicator A x := by
    simp [ap3_term_of_free A hfree x, Finset.sum_ite_eq']
  simp_rw [h_inner, sum_indicator]
  ring

end Counting

end RothsTheorem
