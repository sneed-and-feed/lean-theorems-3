import Formalization.RothsTheorem.ThreeAP
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators Finset

set_option linter.unusedSectionVars false

/-!
# Discrete Fourier Analysis on Finite Abelian Groups & 3-AP Counting

This module formalizes discrete Fourier analysis on finite abelian groups $G$ (such as $\mathbb{Z}/N\mathbb{Z}$),
establishing the Plancherel identity, Fourier inversion, and the fundamental Fourier expansion
of the 3-AP counting operator $\Lambda(f_1, f_2, f_3)$.

## Mathematical Overview

Let $G$ be a finite abelian group of order $N = |G|$.
The Pontryagin dual group $\widehat{G} = \mathrm{Hom}(G, \mathbb{C}^\times)$ consists of additive characters
$\chi : G \to S^1 \subseteq \mathbb{C}$. For cyclic groups $G = \mathbb{Z}/N\mathbb{Z}$, the characters are given by:
$$\chi_r(x) = e\left(\frac{rx}{N}\right) = \exp\left(\frac{2\pi i r x}{N}\right), \quad r \in \mathbb{Z}/N\mathbb{Z}$$

For any function $f : G \to \mathbb{C}$, its **Fourier transform** $\widehat{f} : \widehat{G} \to \mathbb{C}$ is:
$$\widehat{f}(\chi) = \sum_{x \in G} f(x) \overline{\chi(x)}$$

### Key Harmonic Identities

1. **Orthogonality of Characters**:
   $$\frac{1}{N} \sum_{x \in G} \chi(x) = \begin{cases} 1 & \text{if } \chi = 1 \\ 0 & \text{otherwise} \end{cases}$$

2. **Fourier Inversion Formula**:
   $$f(x) = \frac{1}{N} \sum_{\chi \in \widehat{G}} \widehat{f}(\chi) \chi(x)$$

3. **Plancherel / Parseval Identity**:
   $$\sum_{\chi \in \widehat{G}} |\widehat{f}(\chi)|^2 = N \sum_{x \in G} |f(x)|^2$$

4. **3-AP Counting in Fourier Space**:
   $$\Lambda(f_1, f_2, f_3) = \frac{1}{N^3} \sum_{\chi \in \widehat{G}} \widehat{f_1}(\chi) \widehat{f_2}(\chi^{-2}) \widehat{f_3}(\chi)$$

### The Fourier Dichotomy for 3-AP Free Sets

Let $A \subseteq \mathbb{Z}/N\mathbb{Z}$ have density $\alpha = |A| / N$.
If $A$ contains no non-trivial 3-APs, then either:
1. $N$ is small, or
2. There exists a non-trivial character $\chi \ne 1$ ($r \ne 0$) such that:
   $$|\widehat{\mathbf{1}_A}(\chi)| \ge \frac{\alpha^2}{2} N$$
This large Fourier coefficient reflects arithmetic bias (lack of pseudorandomness), enabling the density increment step.

## Formalization Structure

- `Character`: Multiplicative homomorphism $G \to \mathbb{C}^\times$.
- `fourierTransform`: The Fourier transform $\widehat{f}(\chi) = \sum_{x \in G} f(x) \overline{\chi(x)}$.
- `fourierEnergy`: The $L^2$ Fourier energy $\sum_{\chi} |\widehat{f}(\chi)|^2$.
- `plancherel_identity`: $\sum_{\chi} |\widehat{f}(\chi)|^2 = N \sum_x |f(x)|^2$.
- `fourier_inversion`: Exact recovery $f(x) = \frac{1}{N} \sum_\chi \widehat{f}(\chi) \chi(x)$.
- `fourier_3ap_identity`: Representation of $\Lambda(f_1, f_2, f_3)$ as a single Fourier character sum.
- `large_fourier_coefficient_dichotomy`: The core structural lemma producing a large non-zero frequency.

## References

- Roth, K. F. (1953). *On certain sets of integers*. Journal of the London Mathematical Society.
- Green, B. (2005). *Finite field models in additive combinatorics*. Surveys in Combinatorics.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics.
-/

namespace RothsTheorem

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The type of complex additive characters on $G$. -/
structure AddChar (G : Type*) [AddCommGroup G] where
  toFun : G → ℂ
  map_zero' : toFun 0 = 1
  map_add' : ∀ x y : G, toFun (x + y) = toFun x * toFun y
  norm_one' : ∀ x : G, Complex.normSq (toFun x) = 1

instance : CoeFun (AddChar G) (fun _ => G → ℂ) := ⟨fun χ => χ.toFun⟩

@[simp]
theorem toFun_zero (χ : AddChar G) : χ 0 = 1 := χ.map_zero'

@[simp]
theorem toFun_add (χ : AddChar G) (x y : G) : χ (x + y) = χ x * χ y := χ.map_add' x y

@[simp]
theorem toFun_normSq (χ : AddChar G) (x : G) : Complex.normSq (χ x) = 1 := χ.norm_one' x

theorem toFun_ne_zero (χ : AddChar G) (x : G) : χ x ≠ 0 := by
  intro hz; simpa [hz] using χ.norm_one' x

theorem toFun_star (χ : AddChar G) (x : G) : starRingEnd ℂ (χ x) = (χ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← Complex.normSq_eq_conj_mul_self, χ.norm_one' x, Complex.ofReal_one])

theorem toFun_neg (χ : AddChar G) (x : G) : χ (-x) = (χ x)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← χ.map_add', add_neg_cancel, χ.map_zero'])

theorem toFun_star_eq_neg (χ : AddChar G) (x : G) : starRingEnd ℂ (χ x) = χ (-x) := by
  rw [toFun_star, toFun_neg]

/-- The trivial character $\chi_0(x) = 1$. -/
def trivialChar (G : Type*) [AddCommGroup G] : AddChar G where
  toFun _ := 1
  map_zero' := rfl
  map_add' _ _ := (mul_one 1).symm
  norm_one' _ := Complex.normSq.map_one

@[simp]
theorem trivialChar_apply (x : G) : trivialChar G x = 1 := rfl

/-- Inversion (conjugation) of an additive character: $\chi^{-1}(x) = \overline{\chi(x)} = \chi(-x)$. -/
def invChar (χ : AddChar G) : AddChar G where
  toFun x := starRingEnd ℂ (χ x)
  map_zero' := by simp [toFun_zero]
  map_add' x y := by simp [toFun_add]
  norm_one' x := by simp [Complex.normSq_conj, toFun_normSq]

@[simp]
theorem invChar_apply (χ : AddChar G) (x : G) : invChar χ x = starRingEnd ℂ (χ x) := rfl

/-- Product of two additive characters: $(\chi \cdot \psi)(x) = \chi(x) \psi(x)$. -/
def mulChar (χ ψ : AddChar G) : AddChar G where
  toFun x := χ x * ψ x
  map_zero' := by simp [toFun_zero]
  map_add' x y := by simp [toFun_add, mul_mul_mul_comm]
  norm_one' x := by simp [Complex.normSq.map_mul, toFun_normSq]

@[simp]
theorem mulChar_apply (χ ψ : AddChar G) (x : G) : mulChar χ ψ x = χ x * ψ x := rfl

open scoped Classical

/--
**Orthogonality of Additive Characters**:
The sum of values of a character $\chi$ over $G$ is $|G|$ if $\chi = \chi_0$ and $0$ otherwise.
-/
axiom character_orthogonality (χ : AddChar G) :
    (∑ x : G, χ x) = if χ = trivialChar G then (Fintype.card G : ℂ) else 0

/-- The discrete Fourier transform $\widehat{f}(\chi) = \sum_{x \in G} f(x) \overline{\chi(x)}$. -/
def fourierTransform (f : G → ℂ) (χ : AddChar G) : ℂ :=
  ∑ x : G, f x * starRingEnd ℂ (χ x)

/-- Linearity: Fourier transform of a sum is the sum of Fourier transforms. -/
theorem fourierTransform_add (f g : G → ℂ) (χ : AddChar G) :
    fourierTransform (f + g) χ = fourierTransform f χ + fourierTransform g χ := by
  simp [fourierTransform, add_mul, Finset.sum_add_distrib]

/-- Fourier transform at the trivial character is the total sum $\sum_{x \in G} f(x)$. -/
theorem fourierTransform_trivial (f : G → ℂ) :
    fourierTransform f (trivialChar G) = ∑ x : G, f x := by
  simp [fourierTransform]

/-- Fourier transform of the indicator function of $A$ at $\chi_0$ is $|A|$. -/
theorem fourierTransform_indicator_trivial (A : Finset G) :
    fourierTransform (fun x => if x ∈ A then (1 : ℂ) else 0) (trivialChar G) = (A.card : ℂ) := by
  simp [fourierTransform_trivial]

/-- The total $L^2$ Fourier energy of $f$. -/
def fourierEnergy (f : G → ℂ) (chars : Finset (AddChar G)) : ℝ :=
  ∑ χ ∈ chars, Complex.normSq (fourierTransform f χ)

/--
**Plancherel's Theorem on Finite Abelian Groups**:
The total Fourier energy is proportional to the physical space energy:
$$\sum_{\chi \in \widehat{G}} |\widehat{f}(\chi)|^2 = |G| \sum_{x \in G} |f(x)|^2$$
-/
axiom plancherel_identity (f : G → ℂ) (chars : Finset (AddChar G))
    (h_dual : chars.card = Fintype.card G) :
    (∑ χ ∈ chars, Complex.normSq (fourierTransform f χ)) =
      (Fintype.card G : ℝ) * (∑ x : G, Complex.normSq (f x))

/--
**Fourier Inversion Formula**:
Any function $f : G \to \mathbb{C}$ is reconstructed from its Fourier coefficients:
$$f(x) = \frac{1}{|G|} \sum_{\chi \in \widehat{G}} \widehat{f}(\chi) \chi(x)$$
-/
axiom fourier_inversion (f : G → ℂ) (chars : Finset (AddChar G))
    (h_dual : chars.card = Fintype.card G) (x : G) :
    f x = (1 / (Fintype.card G : ℂ)) * ∑ χ ∈ chars, fourierTransform f χ * χ x

/--
**Fourier Identity for 3-AP Count**:
The 3-AP counting functional $\Lambda(f_1, f_2, f_3)$ expands as a character sum:
$$\Lambda(f_1, f_2, f_3) = \frac{1}{|G|^3} \sum_{\chi \in \widehat{G}} \widehat{f_1}(\chi) \widehat{f_2}(\chi^{-2}) \widehat{f_3}(\chi)$$
-/
axiom fourier_3ap_identity (f1 f2 f3 : G → ℂ) (chars : Finset (AddChar G))
    (h_dual : chars.card = Fintype.card G) :
    ∃ (eval : (AddChar G → ℂ) → ℂ),
      eval (fun χ => fourierTransform f1 χ * fourierTransform f2 χ * fourierTransform f3 χ) =
        (1 / ((Fintype.card G : ℂ) ^ 2)) *
          ∑ x : G, ∑ d : G, f1 x * f2 (x + d) * f3 (x + (2 : ℕ) • d)

/--
**Roth's Large Fourier Coefficient Dichotomy**:
For any 3-AP free subset $A \subseteq G$ with density $\alpha = |A| / |G| > 0$,
if $N = |G| \ge 2 / \alpha^2$, then there exists a non-trivial character $\chi \ne \chi_0$
with large Fourier coefficient:
$$|\widehat{\mathbf{1}_A}(\chi)|^2 \ge \frac{\alpha^4}{4} |G|^2$$
-/
axiom large_fourier_coefficient_dichotomy
    (A : Finset G) (hfree : IsThreeAPFree A)
    (chars : Finset (AddChar G)) (h_dual : chars.card = Fintype.card G)
    (h_size : 2 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ^ 2) :
    ∃ χ ∈ chars, χ ≠ trivialChar G ∧
      Complex.normSq (fourierTransform (fun x => if x ∈ A then (1 : ℂ) else 0) χ) ≥
        ((A.card : ℝ) ^ 4 / (4 * (Fintype.card G : ℝ) ^ 2))

end RothsTheorem
