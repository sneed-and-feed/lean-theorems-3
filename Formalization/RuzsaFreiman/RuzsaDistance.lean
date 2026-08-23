import Formalization.RuzsaFreiman.Basic
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise

set_option linter.unusedSectionVars false

/-!
# Ruzsa Distance and the Ruzsa Triangle Inequality

This module formalizes the **Ruzsa Distance** and the **Ruzsa Triangle Inequality** (Imre Z. Ruzsa, 1996),
which endows the space of finite subsets of an abelian group with a pseudometric structure.

## Mathematical Overview

For any two non-empty finite subsets $A, B$ of an additive abelian group $G$:
1. The **Ruzsa multiplicative ratio** is:
   $$\rho_R(A, B) = \frac{|A - B|}{\sqrt{|A| |B|}}$$
2. The **Ruzsa distance** is defined as:
   $$d_R(A, B) = \log \rho_R(A, B) = \log \frac{|A - B|}{\sqrt{|A| |B|}}$$

### Fundamental Properties

1. **Symmetry**: Since $|A - B| = |B - A|$, $d_R(A, B) = d_R(B, A)$.
2. **Translation Invariance**: For any $x, y \in G$, $d_R(A + x, B + y) = d_R(A, B)$.
3. **Non-negativity**: Since $|A - B| \ge \max(|A|, |B|) \ge \sqrt{|A| |B|}$, we have $\rho_R(A, B) \ge 1$ and $d_R(A, B) \ge 0$.
4. **Identity**: $d_R(A, A) = 0$ if and only if $A$ is a coset of a finite subgroup $H \le G$.
5. **Ruzsa Triangle Inequality**: For any finite subsets $A, B, C \subseteq G$:
   $$|B| \cdot |A - C| \le |A - B| \cdot |B - C|$$
   Taking logarithms, this translates into the standard triangle inequality for metric spaces:
   $$d_R(A, C) \le d_R(A, B) + d_R(B, C)$$

## Formalization Structure

- `ruzsaRatio`: The multiplicative ratio $\frac{|A - B|}{\sqrt{|A| |B|}}$.
- `ruzsaDistance`: The log-distance $d_R(A, B)$.
- `ruzsa_triangle_cardinality`: The fundamental cardinality bound $|B| \cdot |A - C| \le |A - B| \cdot |B - C|$.
- `ruzsa_triangle_inequality`: The logarithmic triangle inequality $d_R(A, C) \le d_R(A, B) + d_R(B, C)$.
- `diffset_le_sq_doubling`: The bound $|A - A| \le \frac{|A + A|^2}{|A|}$.

## References

- Ruzsa, I. Z. (1996). *Sums of finite sets*. Number Theory: New York Seminar, Springer, 281–293.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics.
-/

namespace RuzsaFreiman

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The Ruzsa multiplicative ratio $\rho_R(A, B) = \frac{|A - B|}{\sqrt{|A| |B|}}$. -/
noncomputable def ruzsaRatio (A B : Finset G) : ℝ :=
  (A - B).card / Real.sqrt ((A.card : ℝ) * (B.card : ℝ))

/-- The Ruzsa distance $d_R(A, B) = \log \frac{|A - B|}{\sqrt{|A| |B|}}$. -/
noncomputable def ruzsaDistance (A B : Finset G) : ℝ :=
  Real.log (ruzsaRatio A B)

/-- Difference set has same size under reflection: $|A - B| = |B - A|$. -/
theorem card_diffset_symm (A B : Finset G) :
    (A - B).card = (B - A).card := by
  have h_inj : Function.Injective (fun x : G => -x) := neg_injective
  have : B - A = (A - B).image (fun x => -x) := by
    ext x
    simp only [Finset.mem_sub, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, a, ha, rfl⟩
      refine ⟨a - b, ?_, by simp⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, a, ha, by simp [neg_sub]⟩
  rw [this, Finset.card_image_of_injective _ h_inj]

/-- Symmetry of the Ruzsa distance: $d_R(A, B) = d_R(B, A)$. -/
theorem ruzsaDistance_symm (A B : Finset G) :
    ruzsaDistance A B = ruzsaDistance B A := by
  dsimp [ruzsaDistance, ruzsaRatio]
  rw [card_diffset_symm A B, mul_comm (A.card : ℝ)]

/--
**Ruzsa Triangle Inequality (Cardinality Form)**:
For any finite subsets $A, B, C$ in an additive group $G$:
$$|B| \cdot |A - C| \le |A - B| \cdot |B - C|$$
-/
theorem ruzsa_triangle_cardinality (A B C : Finset G) :
    B.card * (A - C).card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rw [mul_comm B.card, card_diffset_symm B C]
  exact h

/-- Strict positivity of the Ruzsa multiplicative ratio for non-empty sets. -/
theorem ruzsaRatio_pos {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    0 < ruzsaRatio A B := by
  have h_sub : (A - B).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨a - b, Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩⟩
  have h_card_pos : (0 : ℝ) < (A - B).card := Nat.cast_pos.mpr h_sub.card_pos
  have hA_pos : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hB_pos : (0 : ℝ) < B.card := Nat.cast_pos.mpr hB.card_pos
  have h_sqrt_pos : 0 < Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos hA_pos hB_pos)
  exact div_pos h_card_pos h_sqrt_pos

/-- Multiplicative triangle inequality for the Ruzsa ratio. -/
theorem ruzsaRatio_mul_le {A B C : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    ruzsaRatio A C ≤ ruzsaRatio A B * ruzsaRatio B C := by
  dsimp [ruzsaRatio]
  have hA0 : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hB0 : (0 : ℝ) < B.card := Nat.cast_pos.mpr hB.card_pos
  have hC0 : (0 : ℝ) < C.card := Nat.cast_pos.mpr hC.card_pos
  have h_card_ineq : B.card * (A - C).card ≤ (A - B).card * (B - C).card :=
    ruzsa_triangle_cardinality A B C
  have h_card_real : (B.card : ℝ) * ((A - C).card : ℝ) ≤ ((A - B).card : ℝ) * ((B - C).card : ℝ) := by
    have := Nat.cast_le (α := ℝ).mpr h_card_ineq
    push_cast at this
    exact this
  have h_sqrt_AB : Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) = Real.sqrt (A.card : ℝ) * Real.sqrt (B.card : ℝ) :=
    Real.sqrt_mul (Nat.cast_nonneg _) (B.card : ℝ)
  have h_sqrt_BC : Real.sqrt ((B.card : ℝ) * (C.card : ℝ)) = Real.sqrt (B.card : ℝ) * Real.sqrt (C.card : ℝ) :=
    Real.sqrt_mul (Nat.cast_nonneg _) (C.card : ℝ)
  have h_sqrt_AC : Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) = Real.sqrt (A.card : ℝ) * Real.sqrt (C.card : ℝ) :=
    Real.sqrt_mul (Nat.cast_nonneg _) (C.card : ℝ)
  have h_self : Real.sqrt (B.card : ℝ) * Real.sqrt (B.card : ℝ) = (B.card : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have h_denom_prod : Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) * Real.sqrt ((B.card : ℝ) * (C.card : ℝ)) =
      Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) * (B.card : ℝ) := by
    rw [h_sqrt_AB, h_sqrt_BC, h_sqrt_AC]
    calc
      Real.sqrt (A.card : ℝ) * Real.sqrt (B.card : ℝ) * (Real.sqrt (B.card : ℝ) * Real.sqrt (C.card : ℝ))
        = Real.sqrt (A.card : ℝ) * (Real.sqrt (B.card : ℝ) * Real.sqrt (B.card : ℝ)) * Real.sqrt (C.card : ℝ) := by ring
      _ = Real.sqrt (A.card : ℝ) * (B.card : ℝ) * Real.sqrt (C.card : ℝ) := by rw [h_self]
      _ = (Real.sqrt (A.card : ℝ) * Real.sqrt (C.card : ℝ)) * (B.card : ℝ) := by ring
  have h_denom_pos : 0 < Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) * (B.card : ℝ) := by
    have : 0 < Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) := Real.sqrt_pos.mpr (mul_pos hA0 hC0)
    exact mul_pos this hB0
  have h_prod_div : ((A - B).card : ℝ) / Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) *
      (((B - C).card : ℝ) / Real.sqrt ((B.card : ℝ) * (C.card : ℝ))) =
      (((A - B).card : ℝ) * ((B - C).card : ℝ)) / (Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) * (B.card : ℝ)) := by
    rw [div_mul_div_comm, h_denom_prod]
  rw [h_prod_div]
  have h_rew : ((A - C).card : ℝ) / Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) =
      ((B.card : ℝ) * ((A - C).card : ℝ)) / (Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) * (B.card : ℝ)) := by
    have hB_ne : (B.card : ℝ) ≠ 0 := ne_of_gt hB0
    calc
      ((A - C).card : ℝ) / Real.sqrt ((A.card : ℝ) * (C.card : ℝ))
        = (((A - C).card : ℝ) * (B.card : ℝ)) / (Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) * (B.card : ℝ)) := by
          rw [mul_div_mul_right _ _ hB_ne]
      _ = ((B.card : ℝ) * ((A - C).card : ℝ)) / (Real.sqrt ((A.card : ℝ) * (C.card : ℝ)) * (B.card : ℝ)) := by
          rw [mul_comm ((A - C).card : ℝ)]
  rw [h_rew]
  exact div_le_div_of_nonneg_right h_card_real (le_of_lt h_denom_pos)

/--
**Ruzsa Triangle Inequality (Metric Form)**:
For any non-empty finite subsets $A, B, C \subseteq G$:
$$d_R(A, C) \le d_R(A, B) + d_R(B, C)$$
-/
theorem ruzsa_triangle_inequality {A B C : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    ruzsaDistance A C ≤ ruzsaDistance A B + ruzsaDistance B C := by
  dsimp [ruzsaDistance]
  have h_pos_AC : 0 < ruzsaRatio A C := ruzsaRatio_pos hA hC
  have h_pos_AB : 0 < ruzsaRatio A B := ruzsaRatio_pos hA hB
  have h_pos_BC : 0 < ruzsaRatio B C := ruzsaRatio_pos hB hC
  have h_log_add : Real.log (ruzsaRatio A B) + Real.log (ruzsaRatio B C) =
      Real.log (ruzsaRatio A B * ruzsaRatio B C) := by
    rw [Real.log_mul (ne_of_gt h_pos_AB) (ne_of_gt h_pos_BC)]
  rw [h_log_add]
  exact Real.log_le_log h_pos_AC (ruzsaRatio_mul_le hA hB hC)

/--
**Difference Set Doubling Bound**:
For any non-empty finite set $A \subseteq G$,
$$|A - A| \le \frac{|A + A|^2}{|A|}$$
-/
theorem diffset_le_sq_doubling {A : Finset G} (hA : A.Nonempty) :
    (A - A).card ≤ (A + A).card ^ 2 / A.card := by
  have h := Finset.ruzsa_triangle_inequality_sub_add_add A A A
  rw [Nat.le_div_iff_mul_le hA.card_pos, sq]
  exact h

/--
**Iterated Difference Bound**:
For any non-empty finite set $A \subseteq G$ with $|A + A| \le K |A|$,
$|A - A| \le K^2 |A|$.
-/
theorem diffset_bound_of_doubling {A : Finset G} (hA : A.Nonempty) {K : ℝ}
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ((A - A).card : ℝ) ≤ K ^ 2 * (A.card : ℝ) := by
  have h_pos : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have h_ineq : (A - A).card * A.card ≤ (A + A).card * (A + A).card := by
    have h := Finset.ruzsa_triangle_inequality_sub_add_add A A A
    exact h
  have h_real : ((A - A).card : ℝ) * (A.card : ℝ) ≤ ((A + A).card : ℝ) ^ 2 := by
    have h_cast : (( (A - A).card * A.card : ℕ) : ℝ) ≤ (( (A + A).card * (A + A).card : ℕ) : ℝ) :=
      Nat.cast_le.mpr h_ineq
    push_cast at h_cast
    rw [sq]
    exact h_cast
  have hK_nonneg : 0 ≤ K := by
    have : (0 : ℝ) ≤ (A + A).card := Nat.cast_nonneg _
    have := le_trans this hK
    exact nonneg_of_mul_nonneg_left this h_pos
  have h_sq : ((A + A).card : ℝ) ^ 2 ≤ (K * (A.card : ℝ)) ^ 2 := by
    nlinarith
  have h_comb : ((A - A).card : ℝ) * (A.card : ℝ) ≤ (K ^ 2 * (A.card : ℝ)) * (A.card : ℝ) := by
    calc
      ((A - A).card : ℝ) * (A.card : ℝ) ≤ ((A + A).card : ℝ) ^ 2 := h_real
      _ ≤ (K * (A.card : ℝ)) ^ 2 := h_sq
      _ = (K ^ 2 * (A.card : ℝ)) * (A.card : ℝ) := by ring
  exact (mul_le_mul_iff_of_pos_right h_pos).mp h_comb

end RuzsaFreiman
