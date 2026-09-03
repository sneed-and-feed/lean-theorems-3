import Formalization.AlonBoppana.SphericalShell
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix Finset
open Classical

variable {V : Type*} [Fintype V]

namespace AlonBoppana

/-! ### Part 4: Nilli's Radial Profiles and Spherical Shell Test Functions -/

/-- Nilli's geometric radial weight profile $g(k) = (d - 1)^{-k / 2} = (1 / \sqrt{d - 1})^k$. -/
noncomputable def nilliProfile (d : ℕ) (k : ℕ) : ℝ :=
  (1 / Real.sqrt (d - 1 : ℝ)) ^ k

/-- Profile value at radius 0 is 1. -/
theorem nilliProfile_zero (d : ℕ) : nilliProfile d 0 = 1 := by
  simp [nilliProfile]

/-- Step recurrence for Nilli profile: $g(k+1) = g(k) / \sqrt{d-1}$. -/
theorem nilliProfile_succ (d : ℕ) (k : ℕ) :
    nilliProfile d (k + 1) = nilliProfile d k * (1 / Real.sqrt (d - 1 : ℝ)) := by
  unfold nilliProfile
  exact pow_succ (1 / Real.sqrt (d - 1 : ℝ)) k

/-- Positivity of the Nilli profile for $d \ge 2$. -/
theorem nilliProfile_pos (d : ℕ) (hd : 2 ≤ d) (k : ℕ) : 0 < nilliProfile d k := by
  have hd_pos : 0 < (d - 1 : ℝ) := by
    have : (d : ℝ) ≥ 2 := Nat.cast_le.mpr hd
    linarith
  exact pow_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hd_pos)) k

/-- Nonnegativity of the Nilli profile for $d \ge 2$. -/
theorem nilliProfile_nonneg (d : ℕ) (hd : 2 ≤ d) (k : ℕ) : 0 ≤ nilliProfile d k :=
  le_of_lt (nilliProfile_pos d hd k)

/-- Product identity across adjacent shells: $g(k) g(k+1) = \sqrt{d-1} g(k+1)^2$. -/
theorem nilliProfile_mul_succ (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    nilliProfile d k * nilliProfile d (k + 1) = Real.sqrt (d - 1 : ℝ) * (nilliProfile d (k + 1)) ^ 2 := by
  have hd_pos : 0 < (d - 1 : ℝ) := by
    have : (d : ℝ) ≥ 2 := Nat.cast_le.mpr hd
    linarith
  have h_sqrt_ne : Real.sqrt (d - 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_pos)
  rw [nilliProfile_succ]
  set s := Real.sqrt (d - 1 : ℝ)
  set g := nilliProfile d k
  have h_cancel : s * (1 / s) = 1 := mul_one_div_cancel h_sqrt_ne
  calc g * (g * (1 / s))
    _ = g ^ 2 * (s * (1 / s) * (1 / s)) := by rw [h_cancel, one_mul]; ring
    _ = s * (g * (1 / s)) ^ 2 := by ring

/-- Radial test vector supported on the ball of radius $r$ around $x_0$ with profile $g$. -/
noncomputable def radialTestVector (G : SimpleGraph V) (x_0 : V) (g : ℕ → ℝ) (r : ℕ) : V → ℝ :=
  fun v => if G.dist x_0 v ≤ r then g (G.dist x_0 v) else 0

/-- Nilli's localized spherical shell test vector. -/
noncomputable def nilliTestVector (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) : V → ℝ :=
  radialTestVector G x_0 (nilliProfile d) r

/-- Norm squared of a radial test vector decomposed by spherical shells. -/
theorem normSq_radialTestVector (G : SimpleGraph V) (x_0 : V) (g : ℕ → ℝ) (r : ℕ) :
    normSq (radialTestVector G x_0 g r) =
      ∑ j ∈ Finset.range (r + 1), (g j) ^ 2 * (sphericalShell G x_0 j).card := by
  simp only [normSq, innerProduct, radialTestVector, sq]
  have h_split : (∑ v : V, (if G.dist x_0 v ≤ r then g (G.dist x_0 v) else 0) *
      (if G.dist x_0 v ≤ r then g (G.dist x_0 v) else 0)) =
      ∑ v ∈ Finset.filter (fun v => G.dist x_0 v ≤ r) Finset.univ, (g (G.dist x_0 v)) * g (G.dist x_0 v) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [h_split]
  have h_fib : (Finset.filter (fun v => G.dist x_0 v ≤ r) (Finset.univ : Finset V)) =
      Finset.biUnion (Finset.range (r + 1)) (fun j => sphericalShell G x_0 j) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, sphericalShell, Nat.lt_succ_iff]
    constructor
    · intro h; exact ⟨G.dist x_0 v, h, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ha
  rw [h_fib]
  have h_disj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint (fun j => sphericalShell G x_0 j) :=
    fun j1 _ j2 _ hne => sphericalShell_disjoint G x_0 hne
  rw [Finset.sum_biUnion h_disj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h_shell : ∀ v ∈ sphericalShell G x_0 j, g (G.dist x_0 v) * g (G.dist x_0 v) = (g j) ^ 2 := by
    intro v hv
    rw [(sphericalShell_mem_iff G x_0 j v).mp hv, sq]
  rw [Finset.sum_congr rfl h_shell, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Sum of values of a radial test vector decomposed by spherical shells. -/
theorem sum_radialTestVector (G : SimpleGraph V) (x_0 : V) (g : ℕ → ℝ) (r : ℕ) :
    ∑ v : V, radialTestVector G x_0 g r v =
      ∑ j ∈ Finset.range (r + 1), g j * (sphericalShell G x_0 j).card := by
  simp only [radialTestVector]
  have h_split : (∑ v : V, if G.dist x_0 v ≤ r then g (G.dist x_0 v) else 0) =
      ∑ v ∈ Finset.filter (fun v => G.dist x_0 v ≤ r) Finset.univ, g (G.dist x_0 v) := by
    rw [Finset.sum_filter]
  rw [h_split]
  have h_fib : (Finset.filter (fun v => G.dist x_0 v ≤ r) (Finset.univ : Finset V)) =
      Finset.biUnion (Finset.range (r + 1)) (fun j => sphericalShell G x_0 j) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, sphericalShell, Nat.lt_succ_iff]
    constructor
    · intro h; exact ⟨G.dist x_0 v, h, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ha
  rw [h_fib]
  have h_disj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint (fun j => sphericalShell G x_0 j) :=
    fun j1 _ j2 _ hne => sphericalShell_disjoint G x_0 hne
  rw [Finset.sum_biUnion h_disj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h_shell : ∀ v ∈ sphericalShell G x_0 j, g (G.dist x_0 v) = g j :=
    fun v hv => by rw [(sphericalShell_mem_iff G x_0 j v).mp hv]
  rw [Finset.sum_congr rfl h_shell, Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [Fintype V] in
/-- Test vector evaluated inside the support ball. -/
theorem nilliTestVector_apply_of_le (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) {v : V}
    (h : G.dist x_0 v ≤ r) :
    nilliTestVector G d x_0 r v = nilliProfile d (G.dist x_0 v) := by
  simp [nilliTestVector, radialTestVector, h]

omit [Fintype V] in
/-- Test vector evaluates to zero outside the support ball. -/
theorem nilliTestVector_apply_of_gt (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) {v : V}
    (h : r < G.dist x_0 v) :
    nilliTestVector G d x_0 r v = 0 := by
  simp [nilliTestVector, radialTestVector, not_le.mpr h]

omit [Fintype V] in
/-- Test vector evaluated at the center vertex $x_0$ equals 1. -/
theorem nilliTestVector_center (G : SimpleGraph V) (d : ℕ) (x_0 : V) (r : ℕ) :
    nilliTestVector G d x_0 r x_0 = 1 := by
  simp [nilliTestVector, radialTestVector, SimpleGraph.dist_self, nilliProfile]

omit [Fintype V] in
/-- Nilli test vector is point-wise non-negative. -/
theorem nilliTestVector_nonneg (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d) (x_0 : V) (r : ℕ) (v : V) :
    0 ≤ nilliTestVector G d x_0 r v := by
  simp only [nilliTestVector, radialTestVector]
  split_ifs with h
  · exact nilliProfile_nonneg d hd (G.dist x_0 v)
  · rfl

/-- Sum of values of the Nilli test vector is strictly positive. -/
theorem nilliTestVector_sum_pos (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d) (x_0 : V) (r : ℕ) :
    0 < ∑ v : V, nilliTestVector G d x_0 r v := by
  have h_center : 0 < nilliTestVector G d x_0 r x_0 := by
    rw [nilliTestVector_center]
    norm_num
  have h_nonneg : ∀ v ∈ (Finset.univ : Finset V), 0 ≤ nilliTestVector G d x_0 r v :=
    fun v _ => nilliTestVector_nonneg G d hd x_0 r v
  have h_le := Finset.single_le_sum h_nonneg (Finset.mem_univ x_0)
  exact lt_of_lt_of_le h_center h_le

/-! ### Part 5: Two-Ball Separation and Orthogonal Linear Combinations -/

/-- Fundamental algebraic inequality bounding a convex combination of ratios by their minimum. -/
theorem min_le_weighted_ratio (a₁ a₂ b₁ b₂ : ℝ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    min (a₁ / b₁) (a₂ / b₂) ≤ (a₁ + a₂) / (b₁ + b₂) := by
  have hb_sum : 0 < b₁ + b₂ := add_pos hb₁ hb₂
  have h1 : min (a₁ / b₁) (a₂ / b₂) * b₁ ≤ a₁ := by
    have h_min := min_le_left (a₁ / b₁) (a₂ / b₂)
    have h_mul := mul_le_mul_of_nonneg_right h_min (le_of_lt hb₁)
    rw [div_mul_cancel₀ a₁ (ne_of_gt hb₁)] at h_mul
    exact h_mul
  have h2 : min (a₁ / b₁) (a₂ / b₂) * b₂ ≤ a₂ := by
    have h_min := min_le_right (a₁ / b₁) (a₂ / b₂)
    have h_mul := mul_le_mul_of_nonneg_right h_min (le_of_lt hb₂)
    rw [div_mul_cancel₀ a₂ (ne_of_gt hb₂)] at h_mul
    exact h_mul
  have h_add : min (a₁ / b₁) (a₂ / b₂) * (b₁ + b₂) ≤ a₁ + a₂ := by
    calc min (a₁ / b₁) (a₂ / b₂) * (b₁ + b₂)
      _ = min (a₁ / b₁) (a₂ / b₂) * b₁ + min (a₁ / b₁) (a₂ / b₂) * b₂ := mul_add _ _ _
      _ ≤ a₁ + a₂ := add_le_add h1 h2
  exact (le_div_iff₀ hb_sum).mpr h_add

/-- Orthogonal balanced linear combination of two test functions. -/
def orthogonalLinearCombination (f₁ f₂ : V → ℝ) : V → ℝ :=
  fun v => (∑ x : V, f₂ x) * f₁ v - (∑ x : V, f₁ x) * f₂ v

/-- The linear combination $f = (\sum f_2) f_1 - (\sum f_1) f_2$ is orthogonal to the all-ones vector. -/
theorem orthogonalLinearCombination_orthogonal (f₁ f₂ : V → ℝ) :
    isOrthogonalToOnes (orthogonalLinearCombination f₁ f₂) := by
  simp only [isOrthogonalToOnes, orthogonalLinearCombination]
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  ring

/-- Inner product of functions with disjoint supports is zero. -/
theorem innerProduct_disjoint_support {f₁ f₂ : V → ℝ} (h_disj : ∀ v : V, f₁ v * f₂ v = 0) :
    innerProduct f₁ f₂ = 0 := by
  simp only [innerProduct]
  have : (∑ x : V, f₁ x * f₂ x) = ∑ x : V, (0 : ℝ) := Finset.sum_congr rfl (fun x _ => h_disj x)
  rw [this, Finset.sum_const_zero]

/-- Norm squared of orthogonal linear combination with disjoint supports. -/
theorem normSq_disjoint_combination {f₁ f₂ : V → ℝ} (h_disj : ∀ v : V, f₁ v * f₂ v = 0) :
    normSq (orthogonalLinearCombination f₁ f₂) =
      (∑ x : V, f₂ x) ^ 2 * normSq f₁ + (∑ x : V, f₁ x) ^ 2 * normSq f₂ := by
  simp only [normSq, innerProduct, orthogonalLinearCombination]
  have h_term (x : V) : ((∑ y : V, f₂ y) * f₁ x - (∑ y : V, f₁ y) * f₂ x) *
      ((∑ y : V, f₂ y) * f₁ x - (∑ y : V, f₁ y) * f₂ x) =
      (∑ y : V, f₂ y) ^ 2 * (f₁ x * f₁ x) + (∑ y : V, f₁ y) ^ 2 * (f₂ x * f₂ x) := by
    have hx := h_disj x
    calc ((∑ y : V, f₂ y) * f₁ x - (∑ y : V, f₁ y) * f₂ x) *
        ((∑ y : V, f₂ y) * f₁ x - (∑ y : V, f₁ y) * f₂ x)
      _ = (∑ y : V, f₂ y) ^ 2 * (f₁ x * f₁ x) + (∑ y : V, f₁ y) ^ 2 * (f₂ x * f₂ x) -
          2 * (∑ y : V, f₂ y) * (∑ y : V, f₁ y) * (f₁ x * f₂ x) := by ring
      _ = (∑ y : V, f₂ y) ^ 2 * (f₁ x * f₁ x) + (∑ y : V, f₁ y) ^ 2 * (f₂ x * f₂ x) := by
        rw [hx, mul_zero, sub_zero]
  simp_rw [h_term]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Quadratic form of orthogonal linear combination when test functions have no edge cross-terms. -/
theorem quadraticForm_disjoint_combination (G : SimpleGraph V) [DecidableRel G.Adj]
    {f₁ f₂ : V → ℝ} (h_disj_adj : ∀ u w : V, G.Adj u w → f₁ u * f₂ w = 0)
    (h_disj_adj' : ∀ u w : V, G.Adj u w → f₂ u * f₁ w = 0) :
    quadraticForm G (orthogonalLinearCombination f₁ f₂) =
      (∑ x : V, f₂ x) ^ 2 * quadraticForm G f₁ + (∑ x : V, f₁ x) ^ 2 * quadraticForm G f₂ := by
  simp only [quadraticForm, adjacencyMatrix, orthogonalLinearCombination]
  have h_term (u w : V) :
      ((∑ y : V, f₂ y) * f₁ u - (∑ y : V, f₁ y) * f₂ u) *
      (if G.Adj u w then (1 : ℝ) else 0) *
      ((∑ y : V, f₂ y) * f₁ w - (∑ y : V, f₁ y) * f₂ w) =
      (∑ y : V, f₂ y) ^ 2 * (f₁ u * (if G.Adj u w then (1 : ℝ) else 0) * f₁ w) +
      (∑ y : V, f₁ y) ^ 2 * (f₂ u * (if G.Adj u w then (1 : ℝ) else 0) * f₂ w) := by
    split_ifs with hadj
    · have h1 := h_disj_adj u w hadj
      have h2 := h_disj_adj' u w hadj
      calc ((∑ y : V, f₂ y) * f₁ u - (∑ y : V, f₁ y) * f₂ u) * 1 *
          ((∑ y : V, f₂ y) * f₁ w - (∑ y : V, f₁ y) * f₂ w)
        _ = (∑ y : V, f₂ y) ^ 2 * (f₁ u * 1 * f₁ w) + (∑ y : V, f₁ y) ^ 2 * (f₂ u * 1 * f₂ w) -
            (∑ y : V, f₂ y) * (∑ y : V, f₁ y) * (f₁ u * f₂ w + f₂ u * f₁ w) := by ring
        _ = (∑ y : V, f₂ y) ^ 2 * (f₁ u * 1 * f₁ w) + (∑ y : V, f₁ y) ^ 2 * (f₂ u * 1 * f₂ w) := by
          rw [h1, h2, add_zero, mul_zero, sub_zero]
    · ring
  simp_rw [h_term]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Rayleigh quotient of the orthogonal linear combination is bounded below by the minimum of quotients. -/
theorem rayleighQuotient_orthogonalCombination (G : SimpleGraph V) [DecidableRel G.Adj]
    {f₁ f₂ : V → ℝ}
    (h_disj : ∀ v : V, f₁ v * f₂ v = 0)
    (h_disj_adj : ∀ u w : V, G.Adj u w → f₁ u * f₂ w = 0)
    (h_disj_adj' : ∀ u w : V, G.Adj u w → f₂ u * f₁ w = 0)
    (h_pos₁ : 0 < (∑ x : V, f₂ x)^2 * normSq f₁)
    (h_pos₂ : 0 < (∑ x : V, f₁ x)^2 * normSq f₂) :
    min (rayleighQuotient G f₁) (rayleighQuotient G f₂) ≤
      rayleighQuotient G (orthogonalLinearCombination f₁ f₂) := by
  have h_quad := quadraticForm_disjoint_combination G h_disj_adj h_disj_adj'
  have h_norm := normSq_disjoint_combination h_disj
  simp only [rayleighQuotient]
  rw [h_quad, h_norm]
  have h_ratio := min_le_weighted_ratio
    ((∑ x : V, f₂ x)^2 * quadraticForm G f₁)
    ((∑ x : V, f₁ x)^2 * quadraticForm G f₂)
    ((∑ x : V, f₂ x)^2 * normSq f₁)
    ((∑ x : V, f₁ x)^2 * normSq f₂)
    h_pos₁ h_pos₂
  have h_scale₁ : ((∑ x : V, f₂ x)^2 * quadraticForm G f₁) / ((∑ x : V, f₂ x)^2 * normSq f₁) =
      quadraticForm G f₁ / normSq f₁ := by
    have h_c_pos : 0 < (∑ x : V, f₂ x)^2 := by
      rcases mul_pos_iff.mp h_pos₁ with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exfalso; linarith [sq_nonneg (∑ x : V, f₂ x)]
    exact mul_div_mul_left (quadraticForm G f₁) (normSq f₁) (ne_of_gt h_c_pos)
  have h_scale₂ : ((∑ x : V, f₁ x)^2 * quadraticForm G f₂) / ((∑ x : V, f₁ x)^2 * normSq f₂) =
      quadraticForm G f₂ / normSq f₂ := by
    have h_c_pos : 0 < (∑ x : V, f₁ x)^2 := by
      rcases mul_pos_iff.mp h_pos₂ with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exfalso; linarith [sq_nonneg (∑ x : V, f₁ x)]
    exact mul_div_mul_left (quadraticForm G f₂) (normSq f₂) (ne_of_gt h_c_pos)
  rw [h_scale₁, h_scale₂] at h_ratio
  exact h_ratio

omit [Fintype V] in
/-- Disjoint support of localized test vectors centered at distant points ($d(x_0, y_0) \ge 2r + 1$). -/
theorem nilliTestVector_disjoint_support (G : SimpleGraph V) (hconn : G.Connected) (d : ℕ)
    {x_0 y_0 : V} {r : ℕ} (h_sep : 2 * r + 1 ≤ G.dist x_0 y_0) (v : V) :
    nilliTestVector G d x_0 r v * nilliTestVector G d y_0 r v = 0 := by
  simp only [nilliTestVector, radialTestVector]
  split_ifs with h1 h2
  · exfalso
    have h_tri := SimpleGraph.Connected.dist_triangle hconn (u := x_0) (v := v) (w := y_0)
    rw [SimpleGraph.dist_comm (u := v) (v := y_0)] at h_tri
    linarith
  · ring
  · ring
  · ring

omit [Fintype V] in
/-- Absence of edge cross-terms between test vectors centered at distant points ($d(x_0, y_0) \ge 2r + 2$). -/
theorem nilliTestVector_disjoint_adj (G : SimpleGraph V) (hconn : G.Connected) (d : ℕ)
    {x_0 y_0 : V} {r : ℕ} (h_sep : 2 * r + 2 ≤ G.dist x_0 y_0) {u w : V} (hadj : G.Adj u w) :
    nilliTestVector G d x_0 r u * nilliTestVector G d y_0 r w = 0 := by
  simp only [nilliTestVector, radialTestVector]
  split_ifs with h1 h2
  · exfalso
    have h_tri1 := SimpleGraph.Connected.dist_triangle hconn (u := x_0) (v := u) (w := y_0)
    have h_tri2 := SimpleGraph.Connected.dist_triangle hconn (u := u) (v := w) (w := y_0)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h_tri2
    rw [SimpleGraph.dist_comm (u := w) (v := y_0)] at h_tri2
    linarith
  · ring
  · ring
  · ring

/-- Nilli's signed test vector formed by the balanced orthogonal combination of two localized
radial test vectors centered at distant vertices $x_0$ and $y_0$. -/
noncomputable def nilliSignedTestVector (G : SimpleGraph V) (d : ℕ) (x_0 y_0 : V) (r : ℕ) : V → ℝ :=
  orthogonalLinearCombination (nilliTestVector G d x_0 r) (nilliTestVector G d y_0 r)

/-- Nilli's signed test vector is orthogonal to the all-ones vector. -/
theorem nilliSignedTestVector_orthogonal (G : SimpleGraph V) (d : ℕ) (x_0 y_0 : V) (r : ℕ) :
    isOrthogonalToOnes (nilliSignedTestVector G d x_0 y_0 r) :=
  orthogonalLinearCombination_orthogonal (nilliTestVector G d x_0 r) (nilliTestVector G d y_0 r)

/-- Nilli's signed test vector is non-zero when the base points are separated by at least $2r + 1$. -/
theorem nilliSignedTestVector_ne_zero (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d)
    {x_0 y_0 : V} {r : ℕ} (h_sep : 2 * r + 1 ≤ G.dist x_0 y_0) :
    nilliSignedTestVector G d x_0 y_0 r ≠ 0 := by
  intro h_zero
  have h_val : nilliSignedTestVector G d x_0 y_0 r x_0 = 0 := by rw [h_zero]; rfl
  simp only [nilliSignedTestVector, orthogonalLinearCombination] at h_val
  have h1 : nilliTestVector G d x_0 r x_0 = 1 := nilliTestVector_center G d x_0 r
  have h2 : nilliTestVector G d y_0 r x_0 = 0 := by
    apply nilliTestVector_apply_of_gt
    rw [SimpleGraph.dist_comm]
    linarith
  rw [h1, h2, mul_one, mul_zero, sub_zero] at h_val
  have h_pos := nilliTestVector_sum_pos G d hd y_0 r
  linarith

end AlonBoppana
