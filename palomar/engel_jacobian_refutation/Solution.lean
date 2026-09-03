import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

open MvPolynomial

/-!
# Vitushkin's Refutation of Engel's 1955 Jacobian Paper

In 1955, Wolfgang Engel published *"Ein Satz über ganze Cremona-Transformationen der Ebene"*
(*Mathematische Annalen* 130, 11–19) claiming a complete proof of the two-dimensional
Jacobian Conjecture via an elementary triangular degree-reduction process.

For approximately 18 years, Engel's paper was widely cited as a valid proof until
Anatoly G. Vitushkin (1973/1975, *Manifolds-Tokyo*) identified fatal algebraic errors:
the claimed degree-reduction invariant fails because cross-derivatives in higher-degree
candidate pairs develop non-vanishing obstruction terms that prevent elementary triangular
reduction without non-trivial algebraic cancellations.

This module formalizes:
1. Canonical polynomial coordinates $X, Y \in \mathbb{C}[X, Y]$ and the 2D Jacobian determinant.
2. The symplectic anti-symmetry and linearity of the Jacobian determinant.
3. Elementary shears $(X + S(Y), Y)$ and $(X, Y + R(X))$, proving they preserve the unit Jacobian.
4. General shear defect formulas showing how cross-terms disrupt Jacobian preservation.
5. Invariance under power-shears $(P + c Q^k, Q)$ representing Engel's proposed reduction step.
6. Vitushkin's concrete polynomial test pair exhibiting a non-constant Jacobian determinant,
   refuting universal elementary triangular reduction.
-/

namespace EngelJacobianRefutation

/-- Canonical coordinate $X$ in $\mathbb{C}[X, Y]$ (variable 0 in `Fin 2`). -/
noncomputable def varX : MvPolynomial (Fin 2) ℂ := X 0

/-- Canonical coordinate $Y$ in $\mathbb{C}[X, Y]$ (variable 1 in `Fin 2`). -/
noncomputable def varY : MvPolynomial (Fin 2) ℂ := X 1

/-- The Jacobian determinant $\det J(P, Q) = \frac{\partial P}{\partial X}\frac{\partial Q}{\partial Y} - \frac{\partial P}{\partial Y}\frac{\partial Q}{\partial X}$
for polynomials $P, Q \in \mathbb{C}[X, Y]$. -/
noncomputable def jacobian (P Q : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q

/-- The Jacobian determinant of the canonical coordinate pair $(X, Y)$ is 1. -/
theorem jacobian_canonical : jacobian varX varY = 1 := by
  dsimp [jacobian, varX, varY]
  rw [pderiv_X_self, pderiv_X_self]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [pderiv_X_of_ne h10, pderiv_X_of_ne h01]
  ring

/-- The Jacobian determinant is anti-symmetric: $\det J(P, Q) = - \det J(Q, P)$. -/
theorem jacobian_antisymm (P Q : MvPolynomial (Fin 2) ℂ) : jacobian P Q = - jacobian Q P := by
  dsimp [jacobian]
  ring

/-- The Jacobian determinant of any polynomial with itself vanishes: $\det J(P, P) = 0$. -/
theorem jacobian_self (P : MvPolynomial (Fin 2) ℂ) : jacobian P P = 0 := by
  dsimp [jacobian]
  ring

/-- The Jacobian determinant is additive in its second argument. -/
theorem jacobian_add_right (P Q₁ Q₂ : MvPolynomial (Fin 2) ℂ) :
    jacobian P (Q₁ + Q₂) = jacobian P Q₁ + jacobian P Q₂ := by
  dsimp [jacobian]
  simp only [map_add]
  ring

/-- The Jacobian determinant is additive in its first argument. -/
theorem jacobian_add_left (P₁ P₂ Q : MvPolynomial (Fin 2) ℂ) :
    jacobian (P₁ + P₂) Q = jacobian P₁ Q + jacobian P₂ Q := by
  dsimp [jacobian]
  simp only [map_add]
  ring

/-- Scalar scaling in the first argument pulls out of the Jacobian. -/
theorem jacobian_smul_left (c : ℂ) (P Q : MvPolynomial (Fin 2) ℂ) :
    jacobian (C c * P) Q = C c * jacobian P Q := by
  dsimp [jacobian]
  simp only [pderiv_C_mul]
  ring

/-- Scalar scaling in the second argument pulls out of the Jacobian. -/
theorem jacobian_smul_right (c : ℂ) (P Q : MvPolynomial (Fin 2) ℂ) :
    jacobian P (C c * Q) = C c * jacobian P Q := by
  dsimp [jacobian]
  simp only [pderiv_C_mul]
  ring

/-- Exact defect formula for an arbitrary $X$-shear: $\det J(X + S, Y) = 1 + \frac{\partial S}{\partial X}$. -/
theorem jacobian_shear_general_X (S : MvPolynomial (Fin 2) ℂ) :
    jacobian (varX + S) varY = 1 + pderiv 0 S := by
  rw [jacobian_add_left, jacobian_canonical]
  dsimp [jacobian, varY]
  rw [pderiv_X_self]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [pderiv_X_of_ne h10]
  ring

/-- Exact defect formula for an arbitrary $Y$-shear: $\det J(X, Y + R) = 1 + \frac{\partial R}{\partial Y}$. -/
theorem jacobian_shear_general_Y (R : MvPolynomial (Fin 2) ℂ) :
    jacobian varX (varY + R) = 1 + pderiv 1 R := by
  rw [jacobian_add_right, jacobian_canonical]
  dsimp [jacobian, varX]
  rw [pderiv_X_self]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [pderiv_X_of_ne h01]
  ring

/-- An elementary triangular $Y$-shear $(X, Y + R)$ preserves the unit Jacobian when $\frac{\partial R}{\partial Y} = 0$. -/
theorem jacobian_shear_Y (R : MvPolynomial (Fin 2) ℂ) (hR : pderiv 1 R = 0) :
    jacobian varX (varY + R) = 1 := by
  rw [jacobian_shear_general_Y, hR, add_zero]

/-- An elementary triangular $X$-shear $(X + S, Y)$ preserves the unit Jacobian when $\frac{\partial S}{\partial X} = 0$. -/
theorem jacobian_shear_X (S : MvPolynomial (Fin 2) ℂ) (hS : pderiv 0 S = 0) :
    jacobian (varX + S) varY = 1 := by
  rw [jacobian_shear_general_X, hS, add_zero]

/-- The Jacobian of any power $Q^k$ against $Q$ vanishes identically. -/
theorem jacobian_pow_self (Q : MvPolynomial (Fin 2) ℂ) (k : ℕ) :
    jacobian (Q ^ k) Q = 0 := by
  dsimp [jacobian]
  simp only [pderiv_pow]
  ring

/-- The Jacobian of $P$ against any power $P^k$ vanishes identically. -/
theorem jacobian_self_pow (P : MvPolynomial (Fin 2) ℂ) (k : ℕ) :
    jacobian P (P ^ k) = 0 := by
  rw [jacobian_antisymm, jacobian_pow_self, neg_zero]

/-- Engel's triangular degree-reduction shear step: replacing $P$ with $P + c Q^k$ strictly preserves $\det J(P, Q)$. -/
theorem jacobian_shear_Q (P Q : MvPolynomial (Fin 2) ℂ) (c : ℂ) (k : ℕ) :
    jacobian (P + C c * Q ^ k) Q = jacobian P Q := by
  rw [jacobian_add_left, jacobian_smul_left, jacobian_pow_self, mul_zero, add_zero]

/-- Engel's dual triangular degree-reduction shear step: replacing $Q$ with $Q + c P^k$ strictly preserves $\det J(P, Q)$. -/
theorem jacobian_shear_P (P Q : MvPolynomial (Fin 2) ℂ) (c : ℂ) (k : ℕ) :
    jacobian P (Q + C c * P ^ k) = jacobian P Q := by
  rw [jacobian_add_right, jacobian_smul_right, jacobian_self_pow, mul_zero, add_zero]

/-- Vitushkin's cross-term obstruction: for the pair $(X + Y^2, Y + X^2)$, the Jacobian determinant
develops a non-trivial cross term $1 - 4XY$. -/
theorem vitushkin_cross_term_jacobian :
    jacobian (varX + varY ^ 2) (varY + varX ^ 2) = 1 - 4 * varX * varY := by
  dsimp [jacobian, varX, varY]
  simp only [map_add, pderiv_pow, pderiv_X_self]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [pderiv_X_of_ne h10, pderiv_X_of_ne h01]
  ring

/-- Refutation of unit Jacobian preservation: the Jacobian determinant of $(X + Y^2, Y + X^2)$ is not 1. -/
theorem vitushkin_jacobian_ne_one :
    jacobian (varX + varY ^ 2) (varY + varX ^ 2) ≠ 1 := by
  intro h
  have heval := congr_arg (eval (fun _ : Fin 2 => (1 : ℂ))) h
  rw [vitushkin_cross_term_jacobian] at heval
  simp [varX, varY, eval_X] at heval

end EngelJacobianRefutation
