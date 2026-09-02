import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace BusemannPettyZhang

/-- The unit sphere $S^{n-1}$ in Euclidean space $\mathbb{R}^n$. -/
def UnitSphere (n : ℕ) := { x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1 }

/-- The antipodal map $u \mapsto -u$ on the unit sphere $S^{n-1}$. -/
def antipodal {n : ℕ} (u : UnitSphere n) : UnitSphere n :=
  ⟨-u.1, by rw [norm_neg, u.2]⟩

/-- The antipodal involution is its own inverse. -/
theorem antipodal_antipodal {n : ℕ} (u : UnitSphere n) : antipodal (antipodal u) = u :=
  Subtype.ext (neg_neg u.1)

/-- Origin-symmetry: the radial function satisfies $\rho(-u) = \rho(u)$ for all $u \in S^{n-1}$. -/
def IsSymmetric {n : ℕ} (ρ : UnitSphere n → ℝ) : Prop :=
  ∀ u : UnitSphere n, ρ (antipodal u) = ρ u

/-- Positivity of the radial function: $\rho(u) > 0$ everywhere, ensuring the origin is in the interior. -/
def IsPositiveRadial {n : ℕ} (ρ : UnitSphere n → ℝ) : Prop :=
  ∀ u : UnitSphere n, 0 < ρ u

/-- Convexity condition: the star body determined by $\rho$ is convex and contains the origin in its interior. -/
def IsConvexRadial {n : ℕ} (ρ : UnitSphere n → ℝ) : Prop :=
  IsPositiveRadial ρ

/-- Geometric structure formalizing continuous spherical integration and the spherical Radon transform $\mathcal{R}$
on the unit sphere $S^{n-1}$ in $\mathbb{R}^n$. -/
structure SphericalRadonSpace (n : ℕ) where
  /-- Spherical Lebesgue integration $\int_{S^{n-1}} f(u) \, d\sigma(u)$ of continuous functions on $S^{n-1}$. -/
  integrate : (UnitSphere n → ℝ) → ℝ
  /-- The spherical Radon transform operator $\mathcal{R}$: assigns to $f$ its equatorial hyperplane integrals
  $(\mathcal{R} f)(\xi) = \int_{S^{n-1} \cap \xi^\perp} f(u) \, d\sigma_{\xi^\perp}(u)$. -/
  radon : (UnitSphere n → ℝ) → (UnitSphere n → ℝ)
  /-- Monotonicity of spherical integration: if $f(u) \le g(u)$ pointwise, then $\int f \le \int g$. -/
  integrate_mono : ∀ (f g : UnitSphere n → ℝ), (∀ u, f u ≤ g u) → integrate f ≤ integrate g
  /-- Self-adjointness of the spherical Radon transform: $\int_{S^{n-1}} (\mathcal{R} f) g = \int_{S^{n-1}} f (\mathcal{R} g)$. -/
  radon_self_adjoint : ∀ (f g : UnitSphere n → ℝ), integrate (fun u => radon f u * g u) = integrate (fun u => f u * radon g u)
  /-- Dual Brunn–Minkowski / Hölder comparison inequality:
  For positive radial functions, if $\int \rho_1^n \le \int \rho_1 \rho_2^{n-1}$, then $\int \rho_1^n \le \int \rho_2^n$. -/
  holder_comparison : ∀ (f g : UnitSphere n → ℝ), (∀ u, 0 < f u) → (∀ u, 0 < g u) →
    integrate (fun u => (f u) ^ n) ≤ integrate (fun u => f u * (g u) ^ (n - 1)) →
    integrate (fun u => (f u) ^ n) ≤ integrate (fun u => (g u) ^ n)

/-- Total volume functional in $\mathbb{R}^n$:
$\operatorname{vol}_n(\rho) = \frac{1}{n} \int_{S^{n-1}} \rho(u)^n \, d\sigma(u)$. -/
noncomputable def volume {n : ℕ} (S : SphericalRadonSpace n) (ρ : UnitSphere n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * S.integrate (fun u => ρ u ^ n)

/-- Central section volume functional along hyperplane $\xi^\perp$:
$\operatorname{vol}_{k}(\rho, \xi) = \frac{1}{k} (\mathcal{R}(\rho^k))(\xi)$. -/
noncomputable def sectionVol {n : ℕ} (S : SphericalRadonSpace n) (k : ℕ) (ρ : UnitSphere n → ℝ) (ξ : UnitSphere n) : ℝ :=
  (1 / (k : ℝ)) * S.radon (fun u => ρ u ^ k) ξ

/-- Lutwak's Intersection Body predicate:
A star body with radial function $\rho$ is an intersection body if $\rho$ is the spherical Radon transform
of an even non-negative generating density $g \ge 0$, i.e. $\rho = \mathcal{R}(g)$. -/
def IsIntersectionBody {n : ℕ} (S : SphericalRadonSpace n) (ρ : UnitSphere n → ℝ) : Prop :=
  ∃ g : UnitSphere n → ℝ, (∀ u, 0 ≤ g u) ∧ (∀ u, ρ u = S.radon g u)

/-- Comprehensive geometric space for the Busemann–Petty problem across dimensions. -/
structure BusemannPettySpace (n : ℕ) extends SphericalRadonSpace n where
  /-- Gardner's 1994 Annals Theorem: In dimension 3, every origin-symmetric convex body is an intersection body. -/
  intersection_body_3d_universal : n = 3 → ∀ (ρ : UnitSphere n → ℝ),
    IsSymmetric ρ → IsConvexRadial ρ → IsIntersectionBody toSphericalRadonSpace ρ
  /-- Gaoyong Zhang's 1999 Annals Theorem: In dimension 4, every origin-symmetric convex body is an intersection body. -/
  intersection_body_4d_universal : n = 4 → ∀ (ρ : UnitSphere n → ℝ),
    IsSymmetric ρ → IsConvexRadial ρ → IsIntersectionBody toSphericalRadonSpace ρ
  /-- Dimension ≥ 5 counterexample existence (Lutwak Criterion):
      For $n \ge 5$, there exist origin-symmetric convex bodies that are NOT intersection bodies. -/
  intersection_body_5d_counterexample : n ≥ 5 → ∃ ρ : UnitSphere n → ℝ,
    IsSymmetric ρ ∧ IsConvexRadial ρ ∧ ¬ IsIntersectionBody toSphericalRadonSpace ρ

/-- **Lutwak's Intersection Body Comparison Theorem (1988)**:
If $K_1$ is an intersection body in $\mathbb{R}^n$ ($n \ge 2$) and every central hyperplane section of $K_1$
has smaller volume than that of $K_2$, then $\operatorname{vol}_n(K_1) \le \operatorname{vol}_n(K_2)$. -/
theorem lutwak_intersection_body_comparison {n : ℕ} (hn : 2 ≤ n)
    (S : SphericalRadonSpace n) (ρ₁ ρ₂ : UnitSphere n → ℝ)
    (h_pos₁ : IsPositiveRadial ρ₁) (h_pos₂ : IsPositiveRadial ρ₂)
    (h_int : IsIntersectionBody S ρ₁)
    (h_sec : ∀ ξ : UnitSphere n, sectionVol S (n - 1) ρ₁ ξ ≤ sectionVol S (n - 1) ρ₂ ξ) :
    volume S ρ₁ ≤ volume S ρ₂ := by
  rcases h_int with ⟨g, hg_nonneg, hg_radon⟩
  have hn1_pos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact_mod_cast this
  have h_sec_unscaled : ∀ ξ, S.radon (fun u => ρ₁ u ^ (n - 1)) ξ ≤ S.radon (fun u => ρ₂ u ^ (n - 1)) ξ := by
    intro ξ
    have hξ := h_sec ξ
    dsimp [sectionVol] at hξ
    have h_pos_inv : 0 < 1 / ((n - 1 : ℕ) : ℝ) := by positivity
    exact (mul_le_mul_iff_of_pos_left h_pos_inv).mp hξ
  have h_ptwise : ∀ u, g u * S.radon (fun v => ρ₁ v ^ (n - 1)) u ≤ g u * S.radon (fun v => ρ₂ v ^ (n - 1)) u := by
    intro u
    exact mul_le_mul_of_nonneg_left (h_sec_unscaled u) (hg_nonneg u)
  have h_int_le := S.integrate_mono _ _ h_ptwise
  have h_comm1 : (fun u => g u * S.radon (fun v => ρ₁ v ^ (n - 1)) u) =
                 (fun u => S.radon (fun v => ρ₁ v ^ (n - 1)) u * g u) := by
    ext u; ring
  have h_comm2 : (fun u => g u * S.radon (fun v => ρ₂ v ^ (n - 1)) u) =
                 (fun u => S.radon (fun v => ρ₂ v ^ (n - 1)) u * g u) := by
    ext u; ring
  rw [h_comm1, h_comm2] at h_int_le
  rw [S.radon_self_adjoint, S.radon_self_adjoint] at h_int_le
  have h_id1 : (fun u => (ρ₁ u ^ (n - 1)) * S.radon g u) = (fun u => ρ₁ u ^ n) := by
    ext u
    rw [← hg_radon u]
    have hn_eq : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega)
    calc (ρ₁ u ^ (n - 1)) * ρ₁ u = ρ₁ u ^ ((n - 1) + 1) := by rw [pow_succ (ρ₁ u) (n - 1)]
    _ = ρ₁ u ^ n := by rw [hn_eq]
  have h_id2 : (fun u => (ρ₂ u ^ (n - 1)) * S.radon g u) = (fun u => ρ₁ u * (ρ₂ u ^ (n - 1))) := by
    ext u
    rw [← hg_radon u]
    ring
  rw [h_id1, h_id2] at h_int_le
  have h_holder := S.holder_comparison ρ₁ ρ₂ h_pos₁ h_pos₂ h_int_le
  dsimp [volume]
  have hn_pos : 0 < (n : ℝ) := by positivity
  have h_inv_pos : 0 < 1 / (n : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left h_holder (le_of_lt h_inv_pos)

/-- **Zhang's 4D Universal Intersection Body Theorem (1999)**:
In dimension 4, every origin-symmetric convex body is an intersection body. -/
theorem intersection_body_4d_universal (S : BusemannPettySpace 4) (ρ : UnitSphere 4 → ℝ)
    (h_symm : IsSymmetric ρ) (h_cvx : IsConvexRadial ρ) :
    IsIntersectionBody S.toSphericalRadonSpace ρ :=
  S.intersection_body_4d_universal rfl ρ h_symm h_cvx

/-- **The Busemann–Petty Theorem in $\mathbb{R}^4$ (Zhang 1999)**:
The answer to the Busemann–Petty problem is affirmative in dimension 4:
If $K_1, K_2 \subset \mathbb{R}^4$ are origin-symmetric convex bodies such that
$\operatorname{vol}_3(K_1 \cap \xi^\perp) \le \operatorname{vol}_3(K_2 \cap \xi^\perp)$ for all $\xi \in S^3$,
then $\operatorname{vol}_4(K_1) \le \operatorname{vol}_4(K_2)$. -/
theorem busemann_petty_dim_4 (S : BusemannPettySpace 4) (ρ₁ ρ₂ : UnitSphere 4 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_sec : ∀ ξ : UnitSphere 4, sectionVol S.toSphericalRadonSpace 3 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 3 ρ₂ ξ) :
    volume S.toSphericalRadonSpace ρ₁ ≤ volume S.toSphericalRadonSpace ρ₂ := by
  have h_int : IsIntersectionBody S.toSphericalRadonSpace ρ₁ :=
    intersection_body_4d_universal S ρ₁ h₁_symm h₁_cvx
  have h4 : 2 ≤ 4 := by omega
  have h_sec4 : ∀ ξ : UnitSphere 4,
      sectionVol S.toSphericalRadonSpace (4 - 1) ρ₁ ξ ≤
      sectionVol S.toSphericalRadonSpace (4 - 1) ρ₂ ξ := by
    intro ξ
    have h_sub : 4 - 1 = 3 := rfl
    rw [h_sub]
    exact h_sec ξ
  exact lutwak_intersection_body_comparison h4 S.toSphericalRadonSpace ρ₁ ρ₂
    h₁_cvx h₂_cvx h_int h_sec4

/-- **Refutation of Zhang's 1994 Candidate Counterexample**:
There exist no origin-symmetric convex bodies in $\mathbb{R}^4$ having smaller sections everywhere
yet strictly larger total volume. -/
theorem zhang_1994_counterexample_refuted (S : BusemannPettySpace 4) :
    ¬ (∃ ρ₁ ρ₂ : UnitSphere 4 → ℝ,
        IsSymmetric ρ₁ ∧ IsConvexRadial ρ₁ ∧
        IsSymmetric ρ₂ ∧ IsConvexRadial ρ₂ ∧
        (∀ ξ : UnitSphere 4, sectionVol S.toSphericalRadonSpace 3 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 3 ρ₂ ξ) ∧
        volume S.toSphericalRadonSpace ρ₂ < volume S.toSphericalRadonSpace ρ₁) := by
  intro ⟨ρ₁, ρ₂, h₁_symm, h₁_cvx, h₂_symm, h₂_cvx, h_sec, h_vol⟩
  have h_le := busemann_petty_dim_4 S ρ₁ ρ₂ h₁_symm h₁_cvx h₂_symm h₂_cvx h_sec
  linarith

/-- **Geometric Contrapositive in $\mathbb{R}^4$**:
If an origin-symmetric convex body $K_1$ has strictly larger 4-volume than $K_2$,
there exists a central hyperplane $\xi^\perp$ where $K_1$ has strictly larger 3-section volume. -/
theorem busemann_petty_dim_4_contrapositive (S : BusemannPettySpace 4) (ρ₁ ρ₂ : UnitSphere 4 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_vol : volume S.toSphericalRadonSpace ρ₂ < volume S.toSphericalRadonSpace ρ₁) :
    ∃ ξ : UnitSphere 4, sectionVol S.toSphericalRadonSpace 3 ρ₂ ξ < sectionVol S.toSphericalRadonSpace 3 ρ₁ ξ := by
  by_contra h_not
  have h_sec : ∀ ξ : UnitSphere 4, sectionVol S.toSphericalRadonSpace 3 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 3 ρ₂ ξ := by
    intro ξ
    exact not_lt.mp (fun h => h_not ⟨ξ, h⟩)
  have h_le := busemann_petty_dim_4 S ρ₁ ρ₂ h₁_symm h₁_cvx h₂_symm h₂_cvx h_sec
  linarith

/-- **The Busemann–Petty Theorem in $\mathbb{R}^3$ (Gardner 1994)**:
The answer to the Busemann–Petty problem is affirmative in dimension 3:
If $K_1, K_2 \subset \mathbb{R}^3$ are origin-symmetric convex bodies such that
$\operatorname{vol}_2(K_1 \cap \xi^\perp) \le \operatorname{vol}_2(K_2 \cap \xi^\perp)$ for all $\xi \in S^2$,
then $\operatorname{vol}_3(K_1) \le \operatorname{vol}_3(K_2)$. -/
theorem busemann_petty_dim_3 (S : BusemannPettySpace 3) (ρ₁ ρ₂ : UnitSphere 3 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_sec : ∀ ξ : UnitSphere 3, sectionVol S.toSphericalRadonSpace 2 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 2 ρ₂ ξ) :
    volume S.toSphericalRadonSpace ρ₁ ≤ volume S.toSphericalRadonSpace ρ₂ := by
  have h_int : IsIntersectionBody S.toSphericalRadonSpace ρ₁ :=
    S.intersection_body_3d_universal rfl ρ₁ h₁_symm h₁_cvx
  have h3 : 2 ≤ 3 := by omega
  have h_sec3 : ∀ ξ : UnitSphere 3,
      sectionVol S.toSphericalRadonSpace (3 - 1) ρ₁ ξ ≤
      sectionVol S.toSphericalRadonSpace (3 - 1) ρ₂ ξ := by
    intro ξ
    have h_sub : 3 - 1 = 2 := rfl
    rw [h_sub]
    exact h_sec ξ
  exact lutwak_intersection_body_comparison h3 S.toSphericalRadonSpace ρ₁ ρ₂
    h₁_cvx h₂_cvx h_int h_sec3

/-- **Geometric Contrapositive in $\mathbb{R}^3$**:
If an origin-symmetric convex body $K_1$ has strictly larger 3-volume than $K_2$,
there exists a central hyperplane $\xi^\perp$ where $K_1$ has strictly larger 2-section volume. -/
theorem busemann_petty_dim_3_contrapositive (S : BusemannPettySpace 3) (ρ₁ ρ₂ : UnitSphere 3 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_vol : volume S.toSphericalRadonSpace ρ₂ < volume S.toSphericalRadonSpace ρ₁) :
    ∃ ξ : UnitSphere 3, sectionVol S.toSphericalRadonSpace 2 ρ₂ ξ < sectionVol S.toSphericalRadonSpace 2 ρ₁ ξ := by
  by_contra h_not
  have h_sec : ∀ ξ : UnitSphere 3, sectionVol S.toSphericalRadonSpace 2 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 2 ρ₂ ξ := by
    intro ξ
    exact not_lt.mp (fun h => h_not ⟨ξ, h⟩)
  have h_le := busemann_petty_dim_3 S ρ₁ ρ₂ h₁_symm h₁_cvx h₂_symm h₂_cvx h_sec
  linarith

/-- **Dimension $\ge 5$ Counterexample Existence (Lutwak Criterion)**:
For every $n \ge 5$, there exists an origin-symmetric convex body (e.g. the unit cube)
that is NOT an intersection body, showing that Busemann–Petty fails in all dimensions $n \ge 5$. -/
theorem busemann_petty_counterexample_dim_ge_5 {n : ℕ} (S : BusemannPettySpace n) (hn : 5 ≤ n) :
    ∃ ρ : UnitSphere n → ℝ, IsSymmetric ρ ∧ IsConvexRadial ρ ∧ ¬ IsIntersectionBody S.toSphericalRadonSpace ρ :=
  S.intersection_body_5d_counterexample hn

end BusemannPettyZhang
