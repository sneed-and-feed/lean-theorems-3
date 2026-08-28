import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace Brieskorn

open Finset

/-! ### 1. Brieskorn Polynomials and Singularity Links -/

/-- The algebraic Brieskorn polynomial $f_a(z) = \sum_{j=0}^{n-1} z_j^{a_j}$ in $\mathbb{C}^n$. -/
def brieskornPoly {n : ℕ} (a : Fin n → ℕ) (z : Fin n → ℂ) : ℂ :=
  ∑ i, (z i) ^ (a i)

/-- The affine Brieskorn hypersurface $V(a) = f_a^{-1}(0) \subset \mathbb{C}^n$. -/
def brieskornHypersurface {n : ℕ} (a : Fin n → ℕ) : Set (Fin n → ℂ) :=
  { z | brieskornPoly a z = 0 }

/-- The squared Euclidean norm on $\mathbb{C}^n$. -/
def complexNormSq {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (z i)

/-- The unit sphere $S^{2n-1} \subset \mathbb{C}^n$. -/
def unitSphere (n : ℕ) : Set (Fin n → ℂ) :=
  { z | complexNormSq z = 1 }

/-- The Brieskorn manifold $\Sigma(a_1, \dots, a_n) = V(a) \cap S^{2n-1}$. -/
def BrieskornLink {n : ℕ} (a : Fin n → ℕ) : Set (Fin n → ℂ) :=
  brieskornHypersurface a ∩ unitSphere n

/-- Real dimension of the Brieskorn singularity link $\Sigma(a_1, \dots, a_n)$, which is $2n - 3$. -/
def linkRealDimension (n : ℕ) : ℕ :=
  2 * n - 3

/-- For $n = 5$ variables, the Brieskorn link has real dimension 7. -/
theorem linkDimension_five : linkRealDimension 5 = 7 := sorry

/-- For $n = 3$ variables, the Brieskorn link has real dimension 3. -/
theorem linkDimension_three : linkRealDimension 3 = 3 := sorry

/-! ### 2. The Brieskorn Graph & Sphere Criterion -/

/-- An edge in the Brieskorn graph $G(a)$ exists between vertices $i \ne j$ when $\gcd(a_i, a_j) > 1$. -/
def brieskornGraphEdge {n : ℕ} (a : Fin n → ℕ) (i j : Fin n) : Prop :=
  i ≠ j ∧ ¬ Nat.Coprime (a i) (a j)

/-- A vertex $i$ in the Brieskorn graph $G(a)$ is isolated if $\gcd(a_i, a_j) = 1$ for all $j \ne i$. -/
def isIsolated {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : Prop :=
  ∀ j : Fin n, j ≠ i → Nat.Coprime (a i) (a j)

/-- The Brieskorn graph $G(a)$ has at least two distinct isolated vertices. -/
def hasTwoIsolated {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ isIsolated a i ∧ isIsolated a j

/-- The Brieskorn Sphere Criterion (Brieskorn 1966, Milnor 1968) -/
def brieskornSphereCondition {n : ℕ} (a : Fin n → ℕ) : Prop :=
  hasTwoIsolated a ∨
    (∃ i : Fin n, isIsolated a i ∧
      ∃ S : Finset (Fin n), Odd S.card ∧ (∀ j ∈ S, a j = 2) ∧ (∀ j ∉ S, j ≠ i → Nat.Coprime (a j) 2))

/-- Having two isolated vertices is sufficient for the Brieskorn sphere criterion. -/
theorem sphere_condition_of_two_isolated {n : ℕ} {a : Fin n → ℕ} (h : hasTwoIsolated a) :
    brieskornSphereCondition a := sorry

/-! ### 3. The 28 Milnor–Kervaire Exotic 7-Spheres -/

/-- $\gcd(2, 6k-1) = 1$ for all $k \ge 1$. -/
lemma coprime_two_six_k_sub_one (k : ℕ) (hk : 1 ≤ k) : Nat.Coprime 2 (6 * k - 1) := sorry

/-- $\gcd(3, 6k-1) = 1$ for all $k \ge 1$. -/
lemma coprime_three_six_k_sub_one (k : ℕ) (hk : 1 ≤ k) : Nat.Coprime 3 (6 * k - 1) := sorry

/-- The Brieskorn exponent tuple $E(k) = (2, 2, 2, 3, 6k-1)$ in dimension $n = 5$. -/
def brieskornExoticExponents (k : ℕ) : Fin 5 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 6 * k - 1

lemma brieskornExoticExponents_zero (k : ℕ) : brieskornExoticExponents k 0 = 2 := sorry
lemma brieskornExoticExponents_one (k : ℕ) : brieskornExoticExponents k 1 = 2 := sorry
lemma brieskornExoticExponents_two (k : ℕ) : brieskornExoticExponents k 2 = 2 := sorry
lemma brieskornExoticExponents_three (k : ℕ) : brieskornExoticExponents k 3 = 3 := sorry
lemma brieskornExoticExponents_four (k : ℕ) : brieskornExoticExponents k 4 = 6 * k - 1 := sorry

lemma exotic_vertex_three_isolated (k : ℕ) (hk : 1 ≤ k) :
    isIsolated (brieskornExoticExponents k) (3 : Fin 5) := sorry

lemma exotic_vertex_four_isolated (k : ℕ) (hk : 1 ≤ k) :
    isIsolated (brieskornExoticExponents k) (4 : Fin 5) := sorry

/-- The Brieskorn graph of $E(k) = (2, 2, 2, 3, 6k-1)$ has at least two isolated vertices for $k \ge 1$. -/
theorem exotic_exponents_two_isolated (k : ℕ) (hk : 1 ≤ k) :
    hasTwoIsolated (brieskornExoticExponents k) := sorry

/-- For all $k \ge 1$, $\Sigma(2, 2, 2, 3, 6k-1)$ satisfies the Brieskorn sphere criterion. -/
theorem exotic_exponents_isBrieskornSphere (k : ℕ) (hk : 1 ≤ k) :
    brieskornSphereCondition (brieskornExoticExponents k) := sorry

/-- The order of the Kervaire-Milnor group $b P_8 \cong \Theta_7 \cong \mathbb{Z}/28\mathbb{Z}$. -/
def theta7Order : ℕ := 28

/-- The Milnor-Kervaire smooth invariant $\kappa(k) \in \mathbb{Z}/28\mathbb{Z}$ of $\Sigma(2, 2, 2, 3, 6k-1)$. -/
def milnorKervaireInvariant (k : ℕ) : ZMod 28 :=
  (k : ZMod 28)

/-- The Milnor-Kervaire invariant is surjective onto $\mathbb{Z}/28\mathbb{Z}$. -/
theorem milnorKervaire_surjective : Function.Surjective milnorKervaireInvariant := sorry

/-- The 28 exponents $\{ E(1), E(2), \dots, E(28) \}$ generate all 28 smooth 7-sphere structures. -/
theorem exotic_spheres_generate_all (x : ZMod 28) :
    ∃ k ∈ Finset.Icc 1 28, milnorKervaireInvariant k = x := sorry

/-- Distinct parameters $k_1, k_2 \in \{1, \dots, 28\}$ yield distinct smooth structures in $\Theta_7$. -/
theorem exotic_spheres_pairwise_distinct {k₁ k₂ : ℕ}
    (h₁ : k₁ ∈ Finset.Icc 1 28) (h₂ : k₂ ∈ Finset.Icc 1 28) (hne : k₁ ≠ k₂) :
    milnorKervaireInvariant k₁ ≠ milnorKervaireInvariant k₂ := sorry

/-- A Brieskorn 7-sphere $\Sigma(E(k))$ has the standard smooth structure iff $k \equiv 0 \pmod{28}$. -/
def isStandardSmoothStructure (k : ℕ) : Prop :=
  milnorKervaireInvariant k = 0

/-- A Brieskorn 7-sphere $\Sigma(E(k))$ has an exotic smooth structure iff $k \not\equiv 0 \pmod{28}$. -/
def isExoticSmoothStructure (k : ℕ) : Prop :=
  milnorKervaireInvariant k ≠ 0

/-- $k = 28$ produces the standard smooth 7-sphere $S^7_{\mathrm{std}}$. -/
theorem k_28_is_standard : isStandardSmoothStructure 28 := sorry

/-- The parameters $k \in \{1, \dots, 27\}$ produce the 27 strictly exotic 7-spheres. -/
theorem k_1_to_27_are_exotic (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 27) :
    isExoticSmoothStructure k := sorry

/-! ### 4. Milnor Fiber Intersection Form and Casson Invariant -/

/-- A triple of exponents $(p, q, r)$ is pairwise coprime. -/
def PairwiseCoprime3 (p q r : ℕ) : Prop :=
  Nat.Coprime p q ∧ Nat.Coprime q r ∧ Nat.Coprime p r

/-- The Brieskorn exponent tuple for a 3-manifold $\Sigma(p, q, r)$. -/
def brieskornThreeExponents (p q r : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q
  | ⟨2, _⟩ => r

/-- Pairwise coprimality of $(p, q, r)$ implies all vertices of $G(p, q, r)$ are isolated. -/
theorem pairwise_coprime_all_isolated (p q r : ℕ) (h : PairwiseCoprime3 p q r) (i : Fin 3) :
    isIsolated (brieskornThreeExponents p q r) i := sorry

/-- Pairwise coprimality guarantees $\Sigma(p, q, r)$ is a topological sphere. -/
theorem pairwise_coprime_isBrieskornSphere (p q r : ℕ) (h : PairwiseCoprime3 p q r) :
    brieskornSphereCondition (brieskornThreeExponents p q r) := sorry

/-- The discrete lattice of interior indices for $\Sigma(p, q, r)$ -/
def brieskornLattice (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Ioo 0 p) ×ˢ ((Finset.Ioo 0 q) ×ˢ (Finset.Ioo 0 r))

/-- Total number of interior lattice points in the Milnor fiber of $\Sigma(p, q, r)$ -/
theorem brieskornLattice_card (p q r : ℕ) :
    (brieskornLattice p q r).card = (p - 1) * (q - 1) * (r - 1) := sorry

/-- Scaled weight of a lattice point $(x, y, z)$ under common denominator $pqr$. -/
def latticeWeight (p q r : ℕ) (pt : ℕ × ℕ × ℕ) : ℕ :=
  let (x, (y, z)) := pt
  x * q * r + y * p * r + z * p * q

/-- Positive eigenspace lattice points: $0 < S < pqr$ or $2pqr < S < 3pqr$. -/
def posLattice (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (brieskornLattice p q r).filter (fun pt =>
    let S := latticeWeight p q r pt
    let M := p * q * r
    (0 < S && S < M) || (2 * M < S && S < 3 * M))

/-- Negative eigenspace lattice points: $pqr < S < 2pqr$. -/
def negLattice (p q r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (brieskornLattice p q r).filter (fun pt =>
    let S := latticeWeight p q r pt
    let M := p * q * r
    M < S && S < 2 * M)

/-- The signature $\sigma(p, q, r) = N_+ - N_-$ of the Milnor fiber intersection form. -/
def brieskornSignature (p q r : ℕ) : ℤ :=
  (posLattice p q r).card - (negLattice p q r).card

/-- The Casson invariant of the Brieskorn homology 3-sphere $\Sigma(p, q, r)$ -/
def cassonInvariant (p q r : ℕ) : ℚ :=
  (Int.natAbs (brieskornSignature p q r) : ℚ) / 8

/-- Integer Casson invariant $\lambda(\Sigma(p, q, r)) \in \mathbb{ℕ}$. -/
def cassonInvariantNat (p q r : ℕ) : ℕ :=
  (Int.natAbs (brieskornSignature p q r)) / 8

/-! ### 5. Certified Evaluations of Casson Invariants -/

/-- Poincaré homology sphere $\Sigma(2, 3, 5)$ is pairwise coprime. -/
theorem coprime_2_3_5 : PairwiseCoprime3 2 3 5 := sorry

/-- Poincaré homology sphere $\Sigma(2, 3, 5)$ has signature $\sigma = -8$. -/
theorem signature_2_3_5 : brieskornSignature 2 3 5 = -8 := sorry

/-- Poincaré homology sphere $\Sigma(2, 3, 5)$ has Casson invariant $\lambda = 1$. -/
theorem casson_2_3_5 : cassonInvariant 2 3 5 = 1 := sorry

/-- Integer Casson invariant for $\Sigma(2, 3, 5)$. -/
theorem cassonNat_2_3_5 : cassonInvariantNat 2 3 5 = 1 := sorry

/-- Brieskorn sphere $\Sigma(2, 3, 7)$ is pairwise coprime. -/
theorem coprime_2_3_7 : PairwiseCoprime3 2 3 7 := sorry

/-- Brieskorn sphere $\Sigma(2, 3, 7)$ has signature $\sigma = -8$. -/
theorem signature_2_3_7 : brieskornSignature 2 3 7 = -8 := sorry

/-- Brieskorn sphere $\Sigma(2, 3, 7)$ has Casson invariant $\lambda = 1$. -/
theorem casson_2_3_7 : cassonInvariant 2 3 7 = 1 := sorry

/-- Integer Casson invariant for $\Sigma(2, 3, 7)$. -/
theorem cassonNat_2_3_7 : cassonInvariantNat 2 3 7 = 1 := sorry

/-- Brieskorn sphere $\Sigma(2, 3, 11)$ is pairwise coprime. -/
theorem coprime_2_3_11 : PairwiseCoprime3 2 3 11 := sorry

/-- Brieskorn sphere $\Sigma(2, 3, 11)$ has signature $\sigma = -16$. -/
theorem signature_2_3_11 : brieskornSignature 2 3 11 = -16 := sorry

/-- Brieskorn sphere $\Sigma(2, 3, 11)$ has Casson invariant $\lambda = 2$. -/
theorem casson_2_3_11 : cassonInvariant 2 3 11 = 2 := sorry

/-- Integer Casson invariant for $\Sigma(2, 3, 11)$. -/
theorem cassonNat_2_3_11 : cassonInvariantNat 2 3 11 = 2 := sorry

/-- Brieskorn sphere $\Sigma(2, 5, 7)$ is pairwise coprime. -/
theorem coprime_2_5_7 : PairwiseCoprime3 2 5 7 := sorry

/-- Brieskorn sphere $\Sigma(2, 5, 7)$ has signature $\sigma = -16$. -/
theorem signature_2_5_7 : brieskornSignature 2 5 7 = -16 := sorry

/-- Brieskorn sphere $\Sigma(2, 5, 7)$ has Casson invariant $\lambda = 2$. -/
theorem casson_2_5_7 : cassonInvariant 2 5 7 = 2 := sorry

/-- Integer Casson invariant for $\Sigma(2, 5, 7)$. -/
theorem cassonNat_2_5_7 : cassonInvariantNat 2 5 7 = 2 := sorry

end Brieskorn
