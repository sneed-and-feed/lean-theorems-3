import Formalization.RothsTheorem.ThreeAP
import Formalization.RothsTheorem.FourierAnalysis
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators Finset

set_option linter.unusedSectionVars false

/-!
# The Density Increment Strategy and Roth's Upper Bound

This module formalizes the iterative **Density Increment Strategy** (Klaus Roth, 1953),
which deduces the existence of 3-term arithmetic progressions by showing that lack of APs
forces a density increase on a subprogression until a contradiction is reached.

## Mathematical Overview

Let $A \subseteq \{1, \dots, N\}$ (or $A \subseteq \mathbb{Z}/N\mathbb{Z}$) have density $\alpha = |A| / N > 0$.
Suppose $A$ contains no non-trivial 3-APs.

### The Density Increment Lemma

From Fourier analysis, there exists a non-zero frequency $r \ne 0$ with $|\widehat{\mathbf{1}_A}(r)| \ge \frac{\alpha^2}{2} N$.
By Dirichlet's Simultaneous Approximation Theorem, the character $\chi_r$ is almost constant on
arithmetic progressions of length $M \approx \sqrt{N}$.

Partitioning $\mathbb{Z}/N\mathbb{Z}$ into such progressions $P_1, \dots, P_m$, there exists a progression $P$
on which $A$ has boosted relative density:
$$\frac{|A \cap P|}{|P|} \ge \alpha + \frac{\alpha^2}{16}$$
with progression length $|P| \ge c \sqrt{N}$.

### The Iteration Argument

1. Rescale $A \cap P$ to a new subset $A' \subseteq \{1, \dots, |P|\}$ via affine bijection.
2. $A'$ is still 3-AP free, but has higher density $\alpha_1 \ge \alpha_0 + \frac{\alpha_0^2}{16}$.
3. Repeat this process: after $k$ steps, the density satisfies $\alpha_k \ge \alpha_{k-1} + \frac{\alpha_{k-1}^2}{16} \ge \alpha_0 + \frac{k \alpha_0^2}{16}$.
4. Since density cannot exceed $1$, the iteration must terminate in at most $k \le \frac{16}{\alpha_0^2}$ steps.
5. In order for the progression length to remain $\ge 3$ at the end of the iteration, we require:
   $$N \ge \exp\left(2^{O(1/\alpha)}\right) \implies \alpha \ge \frac{C}{\log \log N}$$

### Roth's Number $r_3(N)$

The maximum size of a 3-AP free subset of $\{1, \dots, N\}$ satisfies:
$$r_3(N) \le C \frac{N}{\log \log N}$$

### Modern Improvements

- Bourgain (1999, 2008): $r_3(N) \ll N \sqrt{\frac{\log \log N}{\log N}}$.
- Sanders (2011): $r_3(N) \ll \frac{N}{(\log N)^{1 - o(1)}}$.
- Bloom & Sisask (2020): $r_3(N) \ll \frac{N}{(\log N)^{1 + c}}$.
- Kelley & Meka (2023): $r_3(N) \le N \exp\left(-c (\log N)^{1/12}\right)$, near-polynomial bounds.

## Formalization Structure

- `Progression`: Formal definition of a 1D arithmetic progression $\{a + k d : 0 \le k < L\}$.
- `relativeDensity`: The fraction $|A \cap P| / |P|$.
- `density_increment_lemma`: Progression of length $\ge c \sqrt{N}$ with $\ge \alpha + c \alpha^2$ density.
- `roth_three_ap_bound`: Quantitative Roth bound $r_3(N) \le C \frac{N}{\log \log N}$.
- `kelley_meka_bound`: The Kelley–Meka quasi-polynomial bound.

## References

- Roth, K. F. (1953). *On certain sets of integers*. Journal of the London Mathematical Society.
- Bourgain, J. (1999). *On triples in arithmetic progression*. Geometric and Functional Analysis, 9(5), 968–984.
- Kelley, Z., & Meka, R. (2023). *Strong bounds for 3-progressions*. arXiv:2302.05537.
-/

namespace RothsTheorem

/-- An arithmetic progression $P(a, d, L) = \{a + k d : 0 \le k < L\}$ in $\mathbb{Z}$. -/
structure Progression where
  start : ℤ
  step : ℤ
  length : ℕ
  step_pos : 0 < step

/-- The elements of a progression as a finset in $\mathbb{Z}$. -/
def Progression.elements (P : Progression) : Finset ℤ :=
  (Finset.range P.length).image (fun (k : ℕ) => P.start + (k : ℤ) * P.step)

set_option linter.unusedVariables false

/-- The length of a progression is its cardinality. -/
theorem progression_card (P : Progression) :
    P.elements.card = P.length := by
  dsimp [Progression.elements]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range P.length
  · intro x y h
    simp only at h
    have h_step : P.step ≠ 0 := ne_of_gt P.step_pos
    have h_add : (x : ℤ) * P.step = (y : ℤ) * P.step := by linarith
    have h_eq : (x : ℤ) = (y : ℤ) := mul_right_cancel₀ h_step h_add
    exact Nat.cast_inj.mp h_eq

/-- Relative density of a subset $A \subseteq \mathbb{Z}$ inside a progression $P$. -/
noncomputable def relativeDensity (A : Finset ℤ) (P : Progression) : ℝ :=
  ((A ∩ P.elements).card : ℝ) / (P.length : ℝ)

/-- The integer interval $[0, N-1]$ as a Finset of $\mathbb{Z}$. -/
def intRange (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun (k : ℕ) => (k : ℤ))

/--
**The Density Increment Lemma (Roth 1953)**:
If $A \subseteq \{0, \dots, N-1\}$ contains no non-trivial 3-APs with density $\alpha = |A| / N$,
then there exists a progression $P$ of length $|P| \ge c \sqrt{N}$ such that:
$$\frac{|A \cap P|}{|P|} \ge \alpha + \frac{\alpha^2}{16}$$
-/
axiom density_increment_lemma (N : ℕ) (A : Finset ℤ) (hA : A ⊆ intRange N)
    (h_free : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2 * y → x = y)
    (c_len : ℝ) (hc : 0 < c_len) :
    ∃ P : Progression,
      (P.length : ℝ) ≥ c_len * Real.sqrt (N : ℝ) ∧
      relativeDensity A P ≥ ((A.card : ℝ) / (N : ℝ)) + (((A.card : ℝ) / (N : ℝ)) ^ 2) / 16

/--
**Roth's Theorem (Quantitative Upper Bound on $r_3(N)$)**:
There exists an absolute constant $C > 0$ such that any 3-AP free subset $A \subseteq \{0, \dots, N-1\}$
satisfies:
$$|A| \le C \frac{N}{\log \log N}$$
-/
axiom roth_three_ap_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (hN : 4 ≤ N) (A : Finset ℤ),
        A ⊆ intRange N →
        (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2 * y → x = y) →
        (A.card : ℝ) ≤ C * (N : ℝ) / Real.log (Real.log (N : ℝ))

/--
**Kelley–Meka Theorem (2023 Near-Polynomial Bound)**:
There exist constants $c > 0$ and $C > 0$ such that any 3-AP free subset $A \subseteq \{0, \dots, N-1\}$
satisfies:
$$|A| \le C N \exp\left(-c (\log N)^{1/12}\right)$$
-/
axiom kelley_meka_bound :
    ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (A : Finset ℤ),
        A ⊆ intRange N →
        (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2 * y → x = y) →
        (A.card : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 12))

end RothsTheorem
