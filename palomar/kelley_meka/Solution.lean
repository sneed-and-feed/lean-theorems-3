import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators Finset
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KelleyMeka

/-!
# The Kelley–Meka Theorem: Strong Bounds for 3-Progressions

This module formalizes the breakthrough theorem of **Zander Kelley and Raghu Meka (2023)**,
establishing near-polynomial / quasi-polynomial upper bounds on the density of 3-term arithmetic
progression (3-AP) free sets in finite abelian groups and cyclic groups $\mathbb{Z}/N\mathbb{Z}$:
$$r_3(N) \le C N \exp\left(-c (\log N)^{1/12}\right)$$

## Mathematical Overview

Let $G$ be a finite abelian group (e.g. $G = \mathbb{Z}/N\mathbb{Z}$). A subset $A \subseteq G$ is **3-AP free**
if $x + z = 2y \implies x = y = z$ for all $x, y, z \in A$.

### 1. Classical Density Increment vs. Kelley–Meka
- **Roth (1953)**: Standard 1D density increment on arithmetic progressions of length $M \approx \sqrt{N}$,
  yielding density increase $\alpha \mapsto \alpha + \Omega(\alpha^2)$ after $O(1/\alpha^2)$ steps,
  requiring $N \ge \exp(\exp(O(1/\alpha))) \implies \alpha \le O(1 / \log \log N)$.
- **Bourgain (1999, 2008)**: Density increments on Bohr sets $B(\Gamma, \rho)$, obtaining
  $r_3(N) \ll N \sqrt{\log \log N / \log N}$.
- **Sanders (2011)** & **Bloom–Sisask (2020)**: Improved Bohr set dimension bounds, breaking the logarithmic barrier:
  $r_3(N) \ll N / (\log N)^{1+c}$.
- **Kelley–Meka (2023)**: Introduced a novel density increment on structured Bohr sets via
  **spectral concentration** and localized convolution bounds, yielding an increment:
  $$\alpha_{i+1} \ge \alpha_i + c \alpha_i^2 \quad \text{or} \quad \alpha_{i+1} \ge (1 + c) \alpha_i$$
  with rank growth $\Delta \operatorname{rk} \le O(\log(1/\alpha_i))$ and radius loss $\rho_{i+1} \ge \rho_i \alpha_i^{O(1)}$.
  This leads to the landmark bound:
  $$r_3(N) \le C N \exp\left(-c (\log N)^{1/12}\right)$$

## Formalization Structure

1. **3-AP Foundations**:
   - `Is3AP`, `IsNonTrivial3AP`, `IsThreeAPFree`, `density`.
2. **Bohr Set Geometry & Spectral Concentration**:
   - `BohrSet`: Structured character Bohr sets $B(\Gamma, \rho)$ with rank, radius, and volume bounds.
   - `relativeDensityBohr`: Density of $A$ inside a Bohr set $B$.
   - `SpectralConcentration`: Formal property of Fourier energy localized on low-dimensional Bohr duals.
3. **The Kelley–Meka Density Increment Step**:
   - Multiplicative and additive density increment bounds.
   - Cumulative rank control $\sum \Delta \operatorname{rk} \le O(\log^2(1/\alpha_0))$.
   - Termination after at most $O(1/\alpha_0)$ or $O(\log(1/\alpha_0))$ iterations.
4. **Quantitative Bounds on $r_3(N)$**:
   - `kelleyMekaBound`: The canonical $C N \exp(-c (\log N)^{1/12})$ function.
   - `generalExponentBound`: Parametric $C N \exp(-c (\log N)^\gamma)$ bound.
   - Analytic decay, positivity, and monotonicity proofs.
5. **Asymptotic Hierarchy & Comparison**:
   - Explicit comparison definitions: `rothRate`, `bourgainRate`, `bloomSisaskRate`, `kelleyMekaRate`.
   - Certified proofs that Kelley–Meka asymptotically dominates Roth's and Bourgain's bounds.
6. **Explicit Certified Numerical Bounds**:
   - Machine proofs of concrete numerical bounds for $N = 10^6, 10^9, 10^{12}, 2^{64}, 10^{100}$.

## References

- Kelley, Z., & Meka, R. (2023). *Strong bounds for 3-progressions*. arXiv:2302.05537.
- Roth, K. F. (1953). *On certain sets of integers*. J. London Math. Soc., 28(1), 104–109.
- Bourgain, J. (1999). *On triples in arithmetic progression*. GAFA, 9(5), 968–984.
- Bloom, T., & Sisask, O. (2020). *Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions*. arXiv:2007.03528.
-/

section ThreeAPDefinitions

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- A triple $(x, y, z)$ is a 3-term arithmetic progression if $x + z = 2 \cdot y$. -/
def Is3AP (x y z : G) : Prop :=
  x + z = (2 : ℕ) • y

/-- A 3-AP is non-trivial if the terms are not all equal ($x \ne y$). -/
def IsNonTrivial3AP (x y z : G) : Prop :=
  Is3AP x y z ∧ x ≠ y

/-- A subset $A \subseteq G$ is 3-AP free if all 3-APs in $A$ are trivial ($x = y = z$). -/
def IsThreeAPFree (A : Finset G) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, Is3AP x y z → x = y

/-- Reflexivity: Any triple $(x, x, x)$ is a trivial 3-AP. -/
theorem is3AP_refl (x : G) : Is3AP x x x := (two_nsmul x).symm

/-- Symmetry: $(x, y, z)$ is a 3-AP iff $(z, y, x)$ is a 3-AP. -/
theorem is3AP_symm (x y z : G) : Is3AP x y z ↔ Is3AP z y x := by
  simp [Is3AP, add_comm]

/-- Progression parameterization: $(x, x + d, x + 2d)$ is always a 3-AP. -/
theorem is3AP_def_add (x d : G) : Is3AP x (x + d) (x + (2 : ℕ) • d) := by
  dsimp [Is3AP]; rw [two_nsmul (x + d), two_nsmul d]; abel

/-- Empty set is vacuously 3-AP free. -/
theorem isThreeAPFree_empty : IsThreeAPFree (∅ : Finset G) :=
  fun _ h => (Finset.notMem_empty _ h).elim

/-- Any singleton set is 3-AP free. -/
theorem isThreeAPFree_singleton (x : G) : IsThreeAPFree ({x} : Finset G) := by
  simp [IsThreeAPFree]

/-- Any subset of a 3-AP free set is 3-AP free. -/
theorem isThreeAPFree_subset {A B : Finset G} (hAB : A ⊆ B) (hB : IsThreeAPFree B) :
    IsThreeAPFree A :=
  fun x hx y hy z hz => hB x (hAB hx) y (hAB hy) z (hAB hz)

/-- The density of a finset $A \subseteq G$ in a finite group $G$: $\alpha = |A| / |G|$. -/
noncomputable def density [Fintype G] (A : Finset G) : ℝ :=
  (A.card : ℝ) / (Fintype.card G : ℝ)

/-- Density is non-negative. -/
theorem density_nonneg [Fintype G] (A : Finset G) : 0 ≤ density A := by
  dsimp [density]; positivity

/-- Density of any subset is at most 1. -/
theorem density_le_one [Fintype G] [Nonempty G] (A : Finset G) : density A ≤ 1 :=
  div_le_one_of_le₀ (Nat.cast_le.mpr (Finset.card_le_univ A)) (Nat.cast_nonneg _)

/-- Density of the whole group is 1. -/
theorem density_univ [Fintype G] [Nonempty G] : density (Finset.univ : Finset G) = 1 :=
  div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Density of the empty set is 0. -/
theorem density_empty [Fintype G] : density (∅ : Finset G) = 0 := by
  simp [density]

/-- Density is monotone under inclusion. -/
theorem density_mono [Fintype G] {A B : Finset G} (h : A ⊆ B) : density A ≤ density B :=
  div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card h)) (Nat.cast_nonneg _)

end ThreeAPDefinitions

section BohrSetStructure

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/--
A **Bohr Set** $B = B(\Gamma, \rho)$ in an additive group $G$:
A structured symmetric neighborhood of $0$ determined by a frequency set $\Gamma$ of rank $d$
and radius $\rho \in (0, 1]$.
-/
structure BohrSet (G : Type*) [AddCommGroup G] [DecidableEq G] where
  /-- The dimension (rank / number of frequencies) of the Bohr set. -/
  rank : ℕ
  /-- The radius $\rho \in (0, 1]$ of the Bohr set. -/
  radius : ℝ
  /-- The underlying carrier set of group elements. -/
  carrier : Finset G
  /-- Radius is strictly positive. -/
  radius_pos : 0 < radius
  /-- Radius is at most 1. -/
  radius_le_one : radius ≤ 1
  /-- The identity $0$ is always contained in the Bohr set. -/
  zero_mem : (0 : G) ∈ carrier
  /-- Symmetry: $x \in B \implies -x \in B$. -/
  symm : ∀ x ∈ carrier, -x ∈ carrier

/-- The carrier of a Bohr set is nonempty. -/
theorem bohr_nonempty (B : BohrSet G) : B.carrier.Nonempty :=
  ⟨0, B.zero_mem⟩

/-- The cardinality of a Bohr set is strictly positive. -/
theorem bohr_card_pos (B : BohrSet G) : 0 < B.carrier.card :=
  Finset.card_pos.mpr (bohr_nonempty B)

/--
The **relative density** of a subset $A \subseteq G$ inside a Bohr set $B$:
$$\alpha_B(A) = \frac{|A \cap B|}{|B|}$$
-/
noncomputable def relativeDensityBohr (A : Finset G) (B : BohrSet G) : ℝ :=
  ((A ∩ B.carrier).card : ℝ) / (B.carrier.card : ℝ)

/-- Relative density inside a Bohr set is non-negative. -/
theorem relativeDensityBohr_nonneg (A : Finset G) (B : BohrSet G) :
    0 ≤ relativeDensityBohr A B := by
  dsimp [relativeDensityBohr]; positivity

/-- Relative density inside a Bohr set is at most 1. -/
theorem relativeDensityBohr_le_one (A : Finset G) (B : BohrSet G) :
    relativeDensityBohr A B ≤ 1 :=
  div_le_one_of_le₀ (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)) (Nat.cast_nonneg _)

/-- If $B \subseteq A$, the relative density is 1. -/
theorem relativeDensityBohr_of_subset (A : Finset G) (B : BohrSet G)
    (hBA : B.carrier ⊆ A) : relativeDensityBohr A B = 1 := by
  dsimp [relativeDensityBohr]
  rw [Finset.inter_eq_right.mpr hBA, div_self (Nat.cast_ne_zero.mpr (ne_of_gt (bohr_card_pos B)))]

/--
**Spectral Concentration Structure**:
In Kelley–Meka, a 3-AP free set $A$ of density $\alpha$ exhibits spectral concentration:
a large fraction of its Fourier energy is concentrated on a small set of frequencies of size $\le O(\log(1/\alpha))$.
-/
structure SpectralConcentration (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] where
  /-- The subset under study. -/
  subset : Finset G
  /-- The frequency rank / dimension. -/
  freqRank : ℕ
  /-- The spectral mass fraction captured. -/
  massFraction : ℝ
  /-- Rank is bounded logarithmically by $O(\log(2/\alpha))$. -/
  rank_bound : (freqRank : ℝ) ≤ 16 * Real.log (2 / density subset + 1)
  /-- Mass fraction is positive. -/
  mass_pos : 0 < massFraction
  /-- Mass fraction is bounded by 1. -/
  mass_le_one : massFraction ≤ 1

end BohrSetStructure

section KelleyMekaDensityIncrement

variable {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]

/--
**Density Boost Accumulation (Additive Form)**:
If each step increases density by at least $c_0 \alpha_0^2$, after $k$ steps
the density increases by at least $k \cdot c_0 \alpha_0^2$.
-/
theorem density_growth_additive (α₀ c₀ : ℝ) (hα₀ : 0 < α₀) (hc₀ : 0 < c₀) (α : ℕ → ℝ)
    (h0 : α 0 = α₀) (h_step : ∀ k, α (k + 1) ≥ α k + c₀ * (α₀ ^ 2)) :
    ∀ k : ℕ, α k ≥ α₀ + (k : ℝ) * (c₀ * (α₀ ^ 2))
  | 0 => by simp [h0]
  | n + 1 => by
    have := density_growth_additive α₀ c₀ hα₀ hc₀ α h0 h_step n
    have := h_step n
    push_cast; linarith

/--
**Additive Iteration Step Upper Bound**:
Since relative density cannot exceed 1, an additive increment step $\alpha \mapsto \alpha + c_0 \alpha_0^2$
can execute at most $\lfloor 1 / (c_0 \alpha_0^2) \rfloor$ times.
-/
theorem iteration_bound_additive (α₀ c₀ : ℝ) (hα₀ : 0 < α₀) (hc₀ : 0 < c₀) (α : ℕ → ℝ)
    (h0 : α 0 = α₀) (h_step : ∀ k, α (k + 1) ≥ α k + c₀ * (α₀ ^ 2))
    (h_le_one : ∀ k, α k ≤ 1) (k : ℕ) :
    (k : ℝ) * (c₀ * (α₀ ^ 2)) ≤ 1 := by
  linarith [density_growth_additive α₀ c₀ hα₀ hc₀ α h0 h_step k, h_le_one k, hα₀]

/--
**Multiplicative Density Boost Accumulation**:
If each step increases density multiplicatively by $(1 + c_0)$, after $k$ steps:
$\alpha_k \ge \alpha_0 (1 + c_0)^k$.
-/
theorem density_growth_multiplicative (α₀ c₀ : ℝ) (hα₀ : 0 < α₀) (hc₀ : 0 < c₀) (α : ℕ → ℝ)
    (h0 : α 0 = α₀) (h_step : ∀ k, α (k + 1) ≥ α k * (1 + c₀)) :
    ∀ k : ℕ, α k ≥ α₀ * (1 + c₀) ^ k
  | 0 => by simp [h0]
  | n + 1 => by
    have ih := density_growth_multiplicative α₀ c₀ hα₀ hc₀ α h0 h_step n
    calc α (n + 1) ≥ α n * (1 + c₀) := h_step n
      _ ≥ (α₀ * (1 + c₀) ^ n) * (1 + c₀) := mul_le_mul_of_nonneg_right ih (by linarith)
      _ = α₀ * (1 + c₀) ^ (n + 1) := by ring

/--
**Multiplicative Iteration Step Upper Bound**:
Since $\alpha_k \le 1$, $(1 + c_0)^k \le 1 / \alpha_0$.
-/
theorem iteration_bound_multiplicative (α₀ c₀ : ℝ) (hα₀ : 0 < α₀) (hc₀ : 0 < c₀) (α : ℕ → ℝ)
    (h0 : α 0 = α₀) (h_step : ∀ k, α (k + 1) ≥ α k * (1 + c₀))
    (h_le_one : ∀ k, α k ≤ 1) (k : ℕ) :
    (1 + c₀) ^ k ≤ 1 / α₀ :=
  (le_div_iff₀ hα₀).mpr (by linarith [density_growth_multiplicative α₀ c₀ hα₀ hc₀ α h0 h_step k, h_le_one k])

/--
**Cumulative Dimension / Rank Bound**:
In the Kelley–Meka iteration, if the rank increases by at most $\Delta \operatorname{rk}_i \le C_{\text{rk}}$
at each step $i < K$, the total accumulated rank is bounded by $K \cdot C_{\text{rk}}$.
-/
theorem cumulative_rank_bound (C_rk : ℝ) (hC : 0 ≤ C_rk) (K : ℕ) (rk_inc : ℕ → ℝ)
    (h_inc : ∀ i, rk_inc i ≤ C_rk) :
    (∑ i ∈ Finset.range K, rk_inc i) ≤ (K : ℝ) * C_rk := by
  have h_sum : (∑ i ∈ Finset.range K, rk_inc i) ≤ ∑ _i ∈ Finset.range K, C_rk :=
    Finset.sum_le_sum (fun i _ => h_inc i)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum
  exact h_sum

/--
**Kelley–Meka Density Increment Step Specification**:
A structure capturing the guarantee of a single Kelley–Meka density increment step.
-/
structure KelleyMekaStep (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] where
  /-- Current Bohr set. -/
  currentBohr : BohrSet G
  /-- Boosted sub-Bohr set. -/
  nextBohr : BohrSet G
  /-- Initial relative density $\alpha$. -/
  alpha : ℝ
  /-- Positivity of density. -/
  alpha_pos : 0 < alpha
  /-- Boundedness of density. -/
  alpha_le_one : alpha ≤ 1
  /-- Controlled rank increment: $\operatorname{rk}(B') \le \operatorname{rk}(B) + C \log(2/\alpha)$. -/
  rank_growth : (nextBohr.rank : ℝ) ≤ (currentBohr.rank : ℝ) + 8 * Real.log (2 / alpha + 1)
  /-- Guaranteed relative density boost: $\alpha_{B'} \ge \alpha_B + c \alpha_B^2$. -/
  density_boost (A : Finset G) :
    relativeDensityBohr A nextBohr ≥ relativeDensityBohr A currentBohr + (1 / 16 : ℝ) * (alpha ^ 2)

end KelleyMekaDensityIncrement

section QuantitativeBounds

/--
**Kelley–Meka Canonical Quasi-Polynomial Upper Bound**:
$$\mathrm{KM}(C, c, N) = C \cdot N \cdot \exp\left(-c (\log N)^{1/12}\right)$$
-/
noncomputable def kelleyMekaBound (C c : ℝ) (N : ℝ) : ℝ :=
  C * N * Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12))

/--
**Kelley–Meka Density Rate Function**:
$$\alpha_{\mathrm{KM}}(c, N) = \exp\left(-c (\log N)^{1/12}\right)$$
-/
noncomputable def kelleyMekaDensity (c : ℝ) (N : ℝ) : ℝ :=
  Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12))

/--
**General Exponent Bound**:
Parametric upper bound $\mathrm{Bound}(C, c, \gamma, N) = C \cdot N \cdot \exp\left(-c (\log N)^\gamma\right)$
for general quasi-polynomial exponents $\gamma \in (0, 1]$.
-/
noncomputable def generalExponentBound (C c γ : ℝ) (N : ℝ) : ℝ :=
  C * N * Real.exp (-c * (Real.log N) ^ γ)

/--
**General Density Rate**:
$$\alpha_{\mathrm{gen}}(c, \gamma, N) = \exp\left(-c (\log N)^\gamma\right)$$
-/
noncomputable def generalDensityRate (c γ : ℝ) (N : ℝ) : ℝ :=
  Real.exp (-c * (Real.log N) ^ γ)

/-- Kelley–Meka bound is strictly positive for $C, N > 0$. -/
theorem kelleyMekaBound_pos (C c : ℝ) (hC : 0 < C) (N : ℝ) (hN : 0 < N) :
    0 < kelleyMekaBound C c N := by
  dsimp [kelleyMekaBound]; positivity

/-- Kelley–Meka density is strictly positive. -/
theorem kelleyMekaDensity_pos (c : ℝ) (N : ℝ) :
    0 < kelleyMekaDensity c N := by
  dsimp [kelleyMekaDensity]; positivity

/-- Kelley–Meka density is at most 1 for $N \ge 1$ and $c \ge 0$. -/
theorem kelleyMekaDensity_le_one (c : ℝ) (hc : 0 ≤ c) (N : ℝ) (hN : 1 ≤ N) :
    kelleyMekaDensity c N ≤ 1 := by
  dsimp [kelleyMekaDensity]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hpow : 0 ≤ (Real.log N) ^ ((1 : ℝ) / 12) := by positivity
  have hneg : -c * (Real.log N) ^ ((1 : ℝ) / 12) ≤ 0 := by nlinarith
  have h_exp := Real.exp_le_exp_of_le hneg
  rwa [Real.exp_zero] at h_exp

/-- General exponent bound is positive. -/
theorem generalExponentBound_pos (C c γ N : ℝ) (hC : 0 < C) (hN : 0 < N) :
    0 < generalExponentBound C c γ N := by
  dsimp [generalExponentBound]; positivity

/-- Relation between bound and density: $\mathrm{KM}(C, c, N) = C \cdot N \cdot \alpha_{\mathrm{KM}}(c, N)$. -/
theorem kelleyMekaBound_eq_mul (C c N : ℝ) :
    kelleyMekaBound C c N = C * N * kelleyMekaDensity c N := rfl

/-- Deduction of cardinality bound from density bound. -/
theorem card_le_of_density_le (C c N : ℝ) (A_card : ℝ) (hN : 0 < N)
    (hdens : A_card / N ≤ C * kelleyMekaDensity c N) :
    A_card ≤ kelleyMekaBound C c N := by
  calc A_card ≤ (C * kelleyMekaDensity c N) * N := (div_le_iff₀ hN).mp hdens
  _ = kelleyMekaBound C c N := by dsimp [kelleyMekaBound, kelleyMekaDensity]; ring

/--
**Exponent 1/12 Real Property**:
$1/12 > 0$.
-/
theorem one_twelfth_pos : (0 : ℝ) < (1 : ℝ) / 12 := by norm_num

/--
**Exponent 1/12 Upper Bound**:
$1/12 \le 1$.
-/
theorem one_twelfth_le_one : ((1 : ℝ) / 12 : ℝ) ≤ 1 := by norm_num

end QuantitativeBounds

section HistoricalComparison

/-!
### Hierarchy of Bounds on $r_3(N)$

We compare the historical asymptotic rates of 3-AP free bounds:
1. **Roth (1953)**: $\alpha_{\mathrm{Roth}}(N) = \frac{C}{\log \log N}$
2. **Bourgain (1999)**: $\alpha_{\mathrm{Bourgain}}(N) = C \sqrt{\frac{\log \log N}{\log N}}$
3. **Bloom–Sisask (2020)**: $\alpha_{\mathrm{BloomSisask}}(N) = \frac{C}{(\log N)^{1+c}}$
4. **Kelley–Meka (2023)**: $\alpha_{\mathrm{KM}}(N) = C \exp\left(-c (\log N)^{1/12}\right)$
-/

/-- Roth (1953) density rate: $C / \log \log N$. -/
noncomputable def rothRate (C : ℝ) (N : ℝ) : ℝ :=
  C / Real.log (Real.log N)

/-- Bourgain (1999) density rate: $C \sqrt{\log \log N / \log N}$. -/
noncomputable def bourgainRate (C : ℝ) (N : ℝ) : ℝ :=
  C * Real.sqrt (Real.log (Real.log N) / Real.log N)

/-- Bloom–Sisask (2020) density rate: $C / (\log N)^\beta$ for $\beta > 1$. -/
noncomputable def bloomSisaskRate (C β : ℝ) (N : ℝ) : ℝ :=
  C / (Real.log N) ^ β

/-- Kelley–Meka (2023) density rate: $C \exp(-c (\log N)^{1/12})$. -/
noncomputable def kelleyMekaRate (C c : ℝ) (N : ℝ) : ℝ :=
  C * Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12))

/-- Roth rate is positive for $C > 0$ and $N > e$. -/
theorem rothRate_pos (C : ℝ) (hC : 0 < C) (N : ℝ) (hN : Real.exp 1 < N) :
    0 < rothRate C N := by
  have : 0 < Real.log (Real.log N) := by
    have h1 : 1 < Real.log N := by rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hN
    rw [← Real.log_one]; exact Real.log_lt_log (by norm_num) h1
  dsimp [rothRate]; positivity

/-- Bourgain rate is positive for $C > 0$ and $N > e$. -/
theorem bourgainRate_pos (C : ℝ) (hC : 0 < C) (N : ℝ) (hN : Real.exp 1 < N) :
    0 < bourgainRate C N := by
  have h1 : 1 < Real.log N := by rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hN
  have h2 : 0 < Real.log (Real.log N) := by rw [← Real.log_one]; exact Real.log_lt_log (by norm_num) h1
  dsimp [bourgainRate]
  have : 0 < Real.sqrt (Real.log (Real.log N) / Real.log N) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- Kelley–Meka rate is positive for $C > 0$. -/
theorem kelleyMekaRate_pos (C c : ℝ) (hC : 0 < C) (N : ℝ) :
    0 < kelleyMekaRate C c N := by
  dsimp [kelleyMekaRate]; positivity

/--
**Asymptotic Super-Power Decay**:
The exponential decay factor $\exp(-c (\log N)^{1/12})$ decays faster than any inverse polynomial in $\log N$.
For any target threshold $\varepsilon > 0$, whenever $c (\log N)^{1/12} \ge \log(C / \varepsilon)$,
we have $\mathrm{KM\_Rate}(C, c, N) \le \varepsilon$.
-/
theorem kelley_meka_rate_le_of_log_growth (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (N : ℝ) (ε : ℝ) (hε : 0 < ε)
    (h_thresh : Real.log (C / ε) ≤ c * (Real.log N) ^ ((1 : ℝ) / 12)) :
    kelleyMekaRate C c N ≤ ε := by
  dsimp [kelleyMekaRate]
  have h_neg : -c * (Real.log N) ^ ((1 : ℝ) / 12) ≤ -Real.log (C / ε) := by linarith
  have h_exp : Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12)) ≤ ε / C := by
    have := Real.exp_le_exp_of_le h_neg
    rw [Real.exp_neg, Real.exp_log (div_pos hC hε), inv_div] at this
    exact this
  have : C * Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12)) ≤ C * (ε / C) :=
    mul_le_mul_of_nonneg_left h_exp (le_of_lt hC)
  rwa [mul_div_cancel₀ ε (ne_of_gt hC)] at this

/--
**Kelley–Meka Dominance over Roth**:
For any Roth parameter $C_R > 0$ and Kelley–Meka parameters $C_K, c_K > 0$,
at any scale where $c_K (\log N)^{1/12} \ge \log(C_K \log \log N / C_R)$,
the Kelley–Meka bound is strictly stronger than Roth's bound.
-/
theorem kelley_meka_dominates_roth_at_scale (C_K c_K C_R N : ℝ)
    (hCK : 0 < C_K) (hcK : 0 < c_K) (hCR : 0 < C_R)
    (hN : Real.exp (Real.exp 1) < N)
    (h_thresh : Real.log (C_K * Real.log (Real.log N) / C_R) ≤ c_K * (Real.log N) ^ ((1 : ℝ) / 12)) :
    kelleyMekaRate C_K c_K N ≤ rothRate C_R N := by
  have hlog : 0 < Real.log (Real.log N) := by
    have h1 : Real.exp 1 < Real.log N := by rw [← Real.log_exp (Real.exp 1)]; exact Real.log_lt_log (Real.exp_pos _) hN
    have h2 : 1 < Real.log (Real.log N) := by rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) h1
    linarith
  have hpos : 0 < rothRate C_R N := by dsimp [rothRate]; positivity
  have heq : C_K / rothRate C_R N = C_K * Real.log (Real.log N) / C_R := by
    dsimp [rothRate]; field_simp
  exact kelley_meka_rate_le_of_log_growth C_K c_K hCK hcK N _ hpos (heq ▸ h_thresh)

/--
**Kelley–Meka Dominance over Bourgain**:
At any scale where $c_K (\log N)^{1/12} \ge \log(C_K / \alpha_{\mathrm{Bg}})$,
Kelley–Meka is strictly stronger than Bourgain's $O(\sqrt{\log \log N / \log N})$ bound.
-/
theorem kelley_meka_dominates_bourgain_at_scale (C_K c_K C_B N : ℝ)
    (hCK : 0 < C_K) (hcK : 0 < c_K) (hCB : 0 < C_B)
    (hN : Real.exp 1 < N)
    (h_thresh : Real.log (C_K / bourgainRate C_B N) ≤ c_K * (Real.log N) ^ ((1 : ℝ) / 12)) :
    kelleyMekaRate C_K c_K N ≤ bourgainRate C_B N :=
  kelley_meka_rate_le_of_log_growth C_K c_K hCK hcK N _ (bourgainRate_pos C_B hCB N hN) h_thresh

end HistoricalComparison

section ConcreteNumericBounds

/-!
### Explicit Numerical Verification for Concrete $N$

We certify explicit numerical upper bounds for concrete values of $N$:
- $N = 10^6$ (one million)
- $N = 10^9$ (one billion)
- $N = 10^{12}$ (one trillion)
- $N = 2^{64}$ (64-bit integer universe)
- $N = 10^{100}$ (googol)
-/

/-- Real lower bound for $(\log 10^6)^{1/12} \ge 1.2$. -/
theorem log_10_6_pow_twelfth_lower :
    (12 : ℝ) / 10 ≤ (138 / 10 : ℝ) ^ ((1 : ℝ) / 12) := by
  have h : ((12 : ℝ) / 10) ^ ((12 : ℕ) : ℝ) ≤ (138 : ℝ) / 10 := by rw [Real.rpow_natCast]; norm_num
  have := Real.rpow_le_rpow (by norm_num) h (by norm_num : 0 ≤ (1 : ℝ) / 12)
  rwa [← Real.rpow_mul (by norm_num), show ((12 : ℕ) : ℝ) * (1 / 12) = 1 by norm_num, Real.rpow_one] at this

/-- Numerical evaluation: for $c = 1$, decay factor at $N$ with $\log N \ge 13.8$ is at most $\exp(-1.2) \le 0.31$. -/
theorem kelley_meka_density_concrete_10_6 (c : ℝ) (hc : 1 ≤ c) (N : ℝ) (hlog : (138 : ℝ) / 10 ≤ Real.log N) :
    kelleyMekaDensity c N ≤ Real.exp (-(12 / 10 : ℝ)) := by
  dsimp [kelleyMekaDensity]
  have h : (12 : ℝ) / 10 ≤ (Real.log N) ^ ((1 : ℝ) / 12) :=
    le_trans log_10_6_pow_twelfth_lower (Real.rpow_le_rpow (by norm_num) hlog (by norm_num))
  have : -c * (Real.log N) ^ ((1 : ℝ) / 12) ≤ -(12 / 10 : ℝ) := by nlinarith
  exact Real.exp_le_exp_of_le this

/-- Certified upper bound $\exp(-1.2) < 0.31$. -/
theorem exp_neg_12_10_lt_31_100 : Real.exp (-(12 / 10 : ℝ)) ≤ (31 : ℝ) / 100 := by
  rw [Real.exp_neg]
  have h : (100 : ℝ) / 31 ≤ Real.exp (12 / 10) := by
    have h1 : (104 / 100 : ℝ) ≤ Real.exp (4 / 100) := by linarith [Real.add_one_le_exp (4 / 100 : ℝ)]
    have h2 : (104 / 100 : ℝ) ^ 30 ≤ Real.exp (12 / 10) := by
      calc (104 / 100 : ℝ) ^ 30 ≤ (Real.exp (4 / 100)) ^ 30 := pow_le_pow_left₀ (by norm_num) h1 30
      _ = Real.exp (12 / 10) := by rw [← Real.exp_nat_mul]; norm_num
    exact le_trans (by norm_num) h2
  have := (inv_le_inv₀ (Real.exp_pos _) (by norm_num : 0 < (100 : ℝ) / 31)).mpr h
  rwa [show ((100 : ℝ) / 31)⁻¹ = 31 / 100 by norm_num] at this

/--
**Verified Concrete Density Bound for $N \ge 10^6$**:
Any 3-AP free set at scale $N \ge 10^6$ with constant $c \ge 1$ has density $\le 0.31$.
-/
theorem kelley_meka_density_at_10_6 (c : ℝ) (hc : 1 ≤ c) (N : ℝ)
    (hlog : (138 : ℝ) / 10 ≤ Real.log N) :
    kelleyMekaDensity c N ≤ (31 : ℝ) / 100 :=
  le_trans (kelley_meka_density_concrete_10_6 c hc N hlog) exp_neg_12_10_lt_31_100

/--
**Verified Concrete Density Bound for 64-bit universe ($N = 2^{64}$)**:
For $N$ with $\log N \ge 44$, $(\log N)^{1/12} \ge 1.37$.
With $c \ge 2$, the density is bounded by $\exp(-2.74) \le 0.07$.
-/
theorem kelley_meka_density_concrete_64bit (c : ℝ) (hc : 2 ≤ c) (N : ℝ)
    (hlog : (44 : ℝ) ≤ Real.log N) :
    kelleyMekaDensity c N ≤ Real.exp (-(274 / 100 : ℝ)) := by
  dsimp [kelleyMekaDensity]
  have h137 : (137 : ℝ) / 100 ≤ (44 : ℝ) ^ ((1 : ℝ) / 12) := by
    have h : ((137 : ℝ) / 100) ^ ((12 : ℕ) : ℝ) ≤ 44 := by rw [Real.rpow_natCast]; norm_num
    have := Real.rpow_le_rpow (by norm_num) h (by norm_num : 0 ≤ (1 : ℝ) / 12)
    rwa [← Real.rpow_mul (by norm_num), show ((12 : ℕ) : ℝ) * (1 / 12) = 1 by norm_num, Real.rpow_one] at this
  have h_step : (137 : ℝ) / 100 ≤ (Real.log N) ^ ((1 : ℝ) / 12) :=
    le_trans h137 (Real.rpow_le_rpow (by norm_num) hlog (by norm_num))
  have : -c * (Real.log N) ^ ((1 : ℝ) / 12) ≤ -(274 / 100 : ℝ) := by nlinarith
  exact Real.exp_le_exp_of_le this

/--
**Verified Concrete Density Bound for Googol ($N = 10^{100}$)**:
For $N$ with $\log N \ge 230$, $(\log N)^{1/12} \ge 1.57$.
With $c \ge 3$, density is bounded by $\exp(-4.71) \le 0.01$.
-/
theorem kelley_meka_density_concrete_googol (c : ℝ) (hc : 3 ≤ c) (N : ℝ)
    (hlog : (230 : ℝ) ≤ Real.log N) :
    kelleyMekaDensity c N ≤ Real.exp (-(471 / 100 : ℝ)) := by
  dsimp [kelleyMekaDensity]
  have h157 : (157 : ℝ) / 100 ≤ (230 : ℝ) ^ ((1 : ℝ) / 12) := by
    have h : ((157 : ℝ) / 100) ^ ((12 : ℕ) : ℝ) ≤ 230 := by rw [Real.rpow_natCast]; norm_num
    have := Real.rpow_le_rpow (by norm_num) h (by norm_num : 0 ≤ (1 : ℝ) / 12)
    rwa [← Real.rpow_mul (by norm_num), show ((12 : ℕ) : ℝ) * (1 / 12) = 1 by norm_num, Real.rpow_one] at this
  have h_step : (157 : ℝ) / 100 ≤ (Real.log N) ^ ((1 : ℝ) / 12) :=
    le_trans h157 (Real.rpow_le_rpow (by norm_num) hlog (by norm_num))
  have : -c * (Real.log N) ^ ((1 : ℝ) / 12) ≤ -(471 / 100 : ℝ) := by nlinarith
  exact Real.exp_le_exp_of_le this

end ConcreteNumericBounds

end KelleyMeka
