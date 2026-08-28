import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators Finset
open Classical

set_option linter.unusedSectionVars false

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

/-- Indicator function $\mathbf{1}_A : G \to \mathbb{R}$. -/
def indicator (A : Finset G) : G → ℝ :=
  fun x => if x ∈ A then 1 else 0

variable [Fintype G]

/-- Sum of indicator equals cardinality of the finset. -/
theorem sum_indicator (A : Finset G) : ∑ x : G, indicator A x = (A.card : ℝ) := by
  simp [indicator]

/-- For 3-AP free set $A$, off-diagonal 3-AP product terms vanish. -/
theorem ap3_term_of_free (A : Finset G) (hfree : IsThreeAPFree A) (x d : G) :
    indicator A x * indicator A (x + d) * indicator A (x + (2 : ℕ) • d) =
      if d = 0 then indicator A x else 0 := by
  by_cases hd : d = 0
  · subst hd; simp only [add_zero, nsmul_zero]; dsimp [indicator]; split_ifs <;> ring
  · dsimp [indicator]
    split_ifs with hx hxd hx2d
    · exact (hd (add_left_cancel (a := x) (by simpa using (hfree x hx (x + d) hxd (x + (2 : ℕ) • d) hx2d (is3AP_def_add x d)).symm))).elim
    all_goals ring

/-- The multilinear 3-AP counting functional $\Lambda(f_1, f_2, f_3) = \frac{1}{|G|^2} \sum_{x, d} f_1(x) f_2(x+d) f_3(x+2d)$. -/
noncomputable def ap3Count (f1 f2 f3 : G → ℝ) : ℝ :=
  (1 / ((Fintype.card G : ℝ) ^ 2)) *
    ∑ x : G, ∑ d : G, f1 x * f2 (x + d) * f3 (x + (2 : ℕ) • d)

/-- For a 3-AP free set $A$, the only contributions to $\Lambda(1_A, 1_A, 1_A)$ come from $d = 0$. -/
theorem ap3Count_of_free (A : Finset G) (hfree : IsThreeAPFree A) :
    ap3Count (indicator A) (indicator A) (indicator A) =
      (A.card : ℝ) / ((Fintype.card G : ℝ) ^ 2) := by
  dsimp [ap3Count]
  have h_inner x : (∑ d : G, indicator A x * indicator A (x + d) * indicator A (x + (2 : ℕ) • d)) = indicator A x := by
    simp [ap3_term_of_free A hfree x, Finset.sum_ite_eq']
  simp_rw [h_inner, sum_indicator]
  ring

/-- An arithmetic progression $P(a, d, L) = \{a + k d : 0 \le k < L\}$ in $\mathbb{Z}$. -/
structure Progression where
  start : ℤ
  step : ℤ
  length : ℕ
  step_pos : 0 < step

/-- The elements of a progression as a finset in $\mathbb{Z}$. -/
def Progression.elements (P : Progression) : Finset ℤ :=
  (Finset.range P.length).image (fun (k : ℕ) => P.start + (k : ℤ) * P.step)

/-- The length of a progression is its cardinality. -/
theorem progression_card (P : Progression) :
    P.elements.card = P.length := by
  dsimp [Progression.elements]
  rw [Finset.card_image_of_injective _ (fun x y h => Nat.cast_inj.mp (mul_right_cancel₀ (ne_of_gt P.step_pos) (add_left_cancel h)))]
  exact Finset.card_range P.length

/-- Preservation of 3-APs under affine progression map $k \mapsto a + k d$. -/
theorem progression_is3AP (P : Progression) (k1 k2 k3 : ℤ) :
    (P.start + k1 * P.step) + (P.start + k3 * P.step) = 2 * (P.start + k2 * P.step) ↔
      k1 + k3 = 2 * k2 := by
  have h_step : P.step ≠ 0 := ne_of_gt P.step_pos
  constructor
  · intro h
    have h1 : (k1 + k3) * P.step = (2 * k2) * P.step := by linear_combination h
    exact mul_right_cancel₀ h_step h1
  · intro h
    linear_combination h * P.step

/--
**Density Boost Accumulation**:
If density increases by at least $\alpha_0^2 / 16$ at each step, after $k$ steps
the density has grown by at least $k \alpha_0^2 / 16$.
-/
theorem density_boost_bound (α₀ : ℝ) (hα₀ : 0 < α₀) (α : ℕ → ℝ) (h0 : α 0 = α₀)
    (h_step : ∀ k, α (k + 1) ≥ α k + (α₀ ^ 2) / 16) :
    ∀ k : ℕ, α k ≥ α₀ + (k : ℝ) * ((α₀ ^ 2) / 16) := by
  intro k
  induction k with
  | zero => simp [h0]
  | succ n ih =>
    have := h_step n
    push_cast at *
    linarith

/--
**Iteration Step Upper Bound**:
Since density cannot exceed 1, the number of density increments $k$ satisfies
$k \cdot (\alpha_0^2 / 16) \le 1$, meaning $k \le 16 / \alpha_0^2$.
-/
theorem iteration_step_bound (α₀ : ℝ) (hα₀ : 0 < α₀) (α : ℕ → ℝ) (h0 : α 0 = α₀)
    (h_step : ∀ k, α (k + 1) ≥ α k + (α₀ ^ 2) / 16)
    (h_le_one : ∀ k, α k ≤ 1) (k : ℕ) :
    (k : ℝ) * ((α₀ ^ 2) / 16) ≤ 1 := by
  have := density_boost_bound α₀ hα₀ α h0 h_step k
  have := h_le_one k
  linarith

end RothsTheorem
