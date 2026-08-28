import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace Brieskorn

open Finset

def brieskornLattice (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Ioo 0 p) ×ˢ ((Finset.Ioo 0 q) ×ˢ (Finset.Ioo 0 r))

def latticeWeight (p q r : ℕ) (pt : ℕ × ℕ × ℕ) : ℕ :=
  let (x, (y, z)) := pt
  x * q * r + y * p * r + z * p * q

def posLattice (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (brieskornLattice p q r).filter (fun pt =>
    let S := latticeWeight p q r pt
    let M := p * q * r
    (0 < S && S < M) || (2 * M < S && S < 3 * M))

def negLattice (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (brieskornLattice p q r).filter (fun pt =>
    let S := latticeWeight p q r pt
    let M := p * q * r
    M < S && S < 2 * M)

def brieskornSignature (p q r : ℕ) : ℤ :=
  (posLattice p q r).card - (negLattice p q r).card

def cassonInvariant (p q r : ℕ) : ℚ :=
  (Int.natAbs (brieskornSignature p q r) : ℚ) / 8

def cassonInvariantNat (p q r : ℕ) : ℕ :=
  (Int.natAbs (brieskornSignature p q r)) / 8

theorem signature_2_3_5 : brieskornSignature 2 3 5 = -8 := sorry
theorem casson_2_3_5 : cassonInvariant 2 3 5 = 1 := sorry

theorem signature_2_3_7 : brieskornSignature 2 3 7 = -8 := sorry
theorem casson_2_3_7 : cassonInvariant 2 3 7 = 1 := sorry

theorem signature_2_3_11 : brieskornSignature 2 3 11 = -16 := sorry
theorem casson_2_3_11 : cassonInvariant 2 3 11 = 2 := sorry

theorem signature_2_5_7 : brieskornSignature 2 5 7 = -16 := sorry
theorem casson_2_5_7 : cassonInvariant 2 5 7 = 2 := sorry

end Brieskorn

namespace BrieskornSU2

open Finset

/-! ### 1. Diophantine Angle Triples & Spherical Inequalities -/

/-- Normalized rational angle $k/n \in \mathbb{Q}$. -/
def angleQ (k n : ℕ) : ℚ :=
  (k : ℚ) / (n : ℚ)

/-- Strict spherical triangle angle inequalities in $\mathbb{Q}$ for $(a/p, b/q, c/r)$. -/
def sphericalTriangleInequalitiesQ (p q r a b c : ℕ) : Prop :=
  angleQ a p + angleQ b q > angleQ c r ∧
  angleQ a p + angleQ c r > angleQ b q ∧
  angleQ b q + angleQ c r > angleQ a p ∧
  angleQ a p + angleQ b q + angleQ c r < 2

/-- Cross-multiplied integer spherical triangle inequalities in $\mathbb{N}$. -/
def sphericalTriangleInequalitiesNat (p q r a b c : ℕ) : Prop :=
  a * q * r + b * p * r > c * p * q ∧
  a * q * r + c * p * q > b * p * r ∧
  b * p * r + c * p * q > a * q * r ∧
  a * q * r + b * p * r + c * p * q < 2 * (p * q * r)

/-- A triple of integers $(a, b, c)$ is odd in each component. -/
def isOddTriple (a b c : ℕ) : Prop :=
  a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1

/-- Decidable parity check for a triple of integers. -/
def isOddTripleBool (a b c : ℕ) : Bool :=
  (a % 2 == 1) && (b % 2 == 1) && (c % 2 == 1)

/-- A triple $(a, b, c)$ is a spherical angle triple for $\Sigma(p, q, r)$ -/
def IsSphericalAngleTriple (p q r a b c : ℕ) : Prop :=
  1 ≤ a ∧ a < p ∧
  1 ≤ b ∧ b < q ∧
  1 ≤ c ∧ c < r ∧
  a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧
  a * q * r + b * p * r > c * p * q ∧
  a * q * r + c * p * q > b * p * r ∧
  b * p * r + c * p * q > a * q * r ∧
  a * q * r + b * p * r + c * p * q < 2 * (p * q * r)

abbrev IsDiophantineAngleTriple (p q r a b c : ℕ) : Prop :=
  IsSphericalAngleTriple p q r a b c

instance (p q r a b c : ℕ) : Decidable (IsSphericalAngleTriple p q r a b c) := by
  dsimp [IsSphericalAngleTriple]
  infer_instance

def isSphericalAngleBool (p q r : ℕ) (pt : ℕ × ℕ × ℕ) : Bool :=
  let (a, (b, c)) := pt
  let M := p * q * r
  let Sa := a * q * r
  let Sb := b * p * r
  let Sc := c * p * q
  (a % 2 == 1) && (b % 2 == 1) && (c % 2 == 1) &&
  (Sa + Sb > Sc) &&
  (Sa + Sc > Sb) &&
  (Sb + Sc > Sa) &&
  (Sa + Sb + Sc < 2 * M)

/-- For even $p = 2$ and odd $q, r$, any spherical angle triple satisfies the odd sum condition. -/
theorem sphericalAngleTriple_odd_sum {p q r a b c : ℕ} (hp : p = 2) (hq : q % 2 = 1) (hr : r % 2 = 1)
    (h : IsSphericalAngleTriple p q r a b c) :
    (a * q * r + b * p * r + c * p * q) % 2 = 1 := sorry

/-! ### 2. Finset of Irreducible SU(2) Representations -/

def candidateRepFinset (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.Ico 1 p ×ˢ (Finset.Ico 1 q ×ˢ Finset.Ico 1 r)

theorem candidateRepFinset_card (p q r : ℕ) :
    (candidateRepFinset p q r).card = (p - 1) * (q - 1) * (r - 1) := sorry

def IrredSU2RepSet (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (candidateRepFinset p q r).filter (fun pt => isSphericalAngleBool p q r pt)

def irredRepCount (p q r : ℕ) : ℕ :=
  (IrredSU2RepSet p q r).card

/-! ### 3. Certified Irreducible Representation Counts -/

theorem card_irred_su2_2_3_5 : (IrredSU2RepSet 2 3 5).card = 2 := sorry
theorem card_irredRepSet_2_3_5 : (IrredSU2RepSet 2 3 5).card = 2 := sorry
theorem card_irred_su2_2_3_7 : (IrredSU2RepSet 2 3 7).card = 2 := sorry
theorem card_irredRepSet_2_3_7 : (IrredSU2RepSet 2 3 7).card = 2 := sorry
theorem card_irred_su2_2_3_11 : (IrredSU2RepSet 2 3 11).card = 4 := sorry
theorem card_irredRepSet_2_3_11 : (IrredSU2RepSet 2 3 11).card = 4 := sorry
theorem card_irred_su2_2_5_7 : (IrredSU2RepSet 2 5 7).card = 4 := sorry
theorem card_irredRepSet_2_5_7 : (IrredSU2RepSet 2 5 7).card = 4 := sorry

/-! ### 4. Casson Invariant Identification -/

def cassonSU2 (p q r : ℕ) : ℕ :=
  (IrredSU2RepSet p q r).card / 2

def cassonFromSU2 (p q r : ℕ) : ℕ :=
  cassonSU2 p q r

def cassonFromSU2Rat (p q r : ℕ) : ℚ :=
  ((IrredSU2RepSet p q r).card : ℚ) / 2

theorem cassonSU2_2_3_5 : cassonSU2 2 3 5 = 1 := sorry
theorem cassonSU2_2_3_7 : cassonSU2 2 3 7 = 1 := sorry
theorem cassonSU2_2_3_11 : cassonSU2 2 3 11 = 2 := sorry
theorem cassonSU2_2_5_7 : cassonSU2 2 5 7 = 2 := sorry

theorem casson_su2_eq_brieskorn_2_3_5 :
    cassonSU2 2 3 5 = Brieskorn.cassonInvariantNat 2 3 5 := sorry

theorem casson_su2_eq_brieskorn_2_3_7 :
    cassonSU2 2 3 7 = Brieskorn.cassonInvariantNat 2 3 7 := sorry

theorem casson_su2_eq_brieskorn_2_3_11 :
    cassonSU2 2 3 11 = Brieskorn.cassonInvariantNat 2 3 11 := sorry

theorem casson_su2_eq_brieskorn_2_5_7 :
    cassonSU2 2 5 7 = Brieskorn.cassonInvariantNat 2 5 7 := sorry

theorem cassonRat_su2_eq_brieskorn_2_3_5 :
    cassonFromSU2Rat 2 3 5 = Brieskorn.cassonInvariant 2 3 5 := sorry

theorem cassonRat_su2_eq_brieskorn_2_3_7 :
    cassonFromSU2Rat 2 3 7 = Brieskorn.cassonInvariant 2 3 7 := sorry

theorem cassonRat_su2_eq_brieskorn_2_3_11 :
    cassonFromSU2Rat 2 3 11 = Brieskorn.cassonInvariant 2 3 11 := sorry

theorem cassonRat_su2_eq_brieskorn_2_5_7 :
    cassonFromSU2Rat 2 5 7 = Brieskorn.cassonInvariant 2 5 7 := sorry

/-! ### 5. Fricke-Vogt Trace Variety & SU(2) Central Relation -/

def frickeVogtPoly {R : Type*} [CommRing R] (tx ty tz : R) : R :=
  tx ^ 2 + ty ^ 2 + tz ^ 2 + tx * ty * tz - 4

theorem frickeVogtPoly_perm_xy {R : Type*} [CommRing R] (tx ty tz : R) :
    frickeVogtPoly tx ty tz = frickeVogtPoly ty tx tz := sorry

theorem frickeVogtPoly_perm_yz {R : Type*} [CommRing R] (tx ty tz : R) :
    frickeVogtPoly tx ty tz = frickeVogtPoly tx tz ty := sorry

theorem frickeVogtPoly_perm_xz {R : Type*} [CommRing R] (tx ty tz : R) :
    frickeVogtPoly tx ty tz = frickeVogtPoly tz ty tx := sorry

theorem frickeVogtPoly_cyclic {R : Type*} [CommRing R] (tx ty tz : R) :
    frickeVogtPoly tx ty tz = frickeVogtPoly ty tz tx := sorry

theorem frickeVogt_discriminant_identity {R : Type*} [CommRing R] (tx ty tz : R) :
    (2 * tz + tx * ty) ^ 2 - (4 - tx ^ 2) * (4 - ty ^ 2) = 4 * frickeVogtPoly tx ty tz := sorry

theorem frickeVogt_boundary_zero_rat (tx ty tz : ℚ)
    (h : (2 * tz + tx * ty) ^ 2 = (4 - tx ^ 2) * (4 - ty ^ 2)) :
    frickeVogtPoly tx ty tz = 0 := sorry

theorem frickeVogt_order2_specialization {R : Type*} [CommRing R] (ty tz : R) :
    frickeVogtPoly 0 ty tz = ty ^ 2 + tz ^ 2 - 4 := sorry

theorem frickeVogt_order2_boundary_circle {R : Type*} [CommRing R] (ty tz : R)
    (h : ty ^ 2 + tz ^ 2 = 4) :
    frickeVogtPoly 0 ty tz = 0 := sorry

def centralFiberTrace : ℤ := -2

theorem central_fiber_odd_power (b : ℕ) (hb : b % 2 = 1) :
    (-1 : ℤ) ^ b = -1 := sorry

end BrieskornSU2
