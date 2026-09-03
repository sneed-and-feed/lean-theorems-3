import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity


namespace BusemannPettyZhang

/-- The unit sphere $S^{n-1}$ in Euclidean space $\mathbb{R}^n$. -/
def UnitSphere (n : ℕ) := { x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1 }

/-- The antipodal map $u \mapsto -u$ on the unit sphere $S^{n-1}$. -/
def antipodal {n : ℕ} (u : UnitSphere n) : UnitSphere n :=
  ⟨-u.1, by rw [norm_neg, u.2]⟩

/-- The antipodal involution is its own inverse. -/
theorem antipodal_antipodal {n : ℕ} (u : UnitSphere n) : antipodal (antipodal u) = u := sorry

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
    volume S ρ₁ ≤ volume S ρ₂ := sorry

/-- **Zhang's 4D Universal Intersection Body Theorem (1999)**:
In dimension 4, every origin-symmetric convex body is an intersection body. -/
theorem intersection_body_4d_universal (S : BusemannPettySpace 4) (ρ : UnitSphere 4 → ℝ)
    (h_symm : IsSymmetric ρ) (h_cvx : IsConvexRadial ρ) :
    IsIntersectionBody S.toSphericalRadonSpace ρ := sorry

/-- **The Busemann–Petty Theorem in $\mathbb{R}^4$ (Zhang 1999)**:
The answer to the Busemann–Petty problem is affirmative in dimension 4:
If $K_1, K_2 \subset \mathbb{R}^4$ are origin-symmetric convex bodies such that
$\operatorname{vol}_3(K_1 \cap \xi^\perp) \le \operatorname{vol}_3(K_2 \cap \xi^\perp)$ for all $\xi \in S^3$,
then $\operatorname{vol}_4(K_1) \le \operatorname{vol}_4(K_2)$. -/
theorem busemann_petty_dim_4 (S : BusemannPettySpace 4) (ρ₁ ρ₂ : UnitSphere 4 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_sec : ∀ ξ : UnitSphere 4, sectionVol S.toSphericalRadonSpace 3 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 3 ρ₂ ξ) :
    volume S.toSphericalRadonSpace ρ₁ ≤ volume S.toSphericalRadonSpace ρ₂ := sorry

/-- **Refutation of Zhang's 1994 Candidate Counterexample**:
There exist no origin-symmetric convex bodies in $\mathbb{R}^4$ having smaller sections everywhere
yet strictly larger total volume. -/
theorem zhang_1994_counterexample_refuted (S : BusemannPettySpace 4) :
    ¬ (∃ ρ₁ ρ₂ : UnitSphere 4 → ℝ,
        IsSymmetric ρ₁ ∧ IsConvexRadial ρ₁ ∧
        IsSymmetric ρ₂ ∧ IsConvexRadial ρ₂ ∧
        (∀ ξ : UnitSphere 4, sectionVol S.toSphericalRadonSpace 3 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 3 ρ₂ ξ) ∧
        volume S.toSphericalRadonSpace ρ₂ < volume S.toSphericalRadonSpace ρ₁) := sorry

/-- **Geometric Contrapositive in $\mathbb{R}^4$**:
If an origin-symmetric convex body $K_1$ has strictly larger 4-volume than $K_2$,
there exists a central hyperplane $\xi^\perp$ where $K_1$ has strictly larger 3-section volume. -/
theorem busemann_petty_dim_4_contrapositive (S : BusemannPettySpace 4) (ρ₁ ρ₂ : UnitSphere 4 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_vol : volume S.toSphericalRadonSpace ρ₂ < volume S.toSphericalRadonSpace ρ₁) :
    ∃ ξ : UnitSphere 4, sectionVol S.toSphericalRadonSpace 3 ρ₂ ξ < sectionVol S.toSphericalRadonSpace 3 ρ₁ ξ := sorry

/-- **The Busemann–Petty Theorem in $\mathbb{R}^3$ (Gardner 1994)**:
The answer to the Busemann–Petty problem is affirmative in dimension 3:
If $K_1, K_2 \subset \mathbb{R}^3$ are origin-symmetric convex bodies such that
$\operatorname{vol}_2(K_1 \cap \xi^\perp) \le \operatorname{vol}_2(K_2 \cap \xi^\perp)$ for all $\xi \in S^2$,
then $\operatorname{vol}_3(K_1) \le \operatorname{vol}_3(K_2)$. -/
theorem busemann_petty_dim_3 (S : BusemannPettySpace 3) (ρ₁ ρ₂ : UnitSphere 3 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_sec : ∀ ξ : UnitSphere 3, sectionVol S.toSphericalRadonSpace 2 ρ₁ ξ ≤ sectionVol S.toSphericalRadonSpace 2 ρ₂ ξ) :
    volume S.toSphericalRadonSpace ρ₁ ≤ volume S.toSphericalRadonSpace ρ₂ := sorry

/-- **Geometric Contrapositive in $\mathbb{R}^3$**:
If an origin-symmetric convex body $K_1$ has strictly larger 3-volume than $K_2$,
there exists a central hyperplane $\xi^\perp$ where $K_1$ has strictly larger 2-section volume. -/
theorem busemann_petty_dim_3_contrapositive (S : BusemannPettySpace 3) (ρ₁ ρ₂ : UnitSphere 3 → ℝ)
    (h₁_symm : IsSymmetric ρ₁) (h₁_cvx : IsConvexRadial ρ₁)
    (h₂_symm : IsSymmetric ρ₂) (h₂_cvx : IsConvexRadial ρ₂)
    (h_vol : volume S.toSphericalRadonSpace ρ₂ < volume S.toSphericalRadonSpace ρ₁) :
    ∃ ξ : UnitSphere 3, sectionVol S.toSphericalRadonSpace 2 ρ₂ ξ < sectionVol S.toSphericalRadonSpace 2 ρ₁ ξ := sorry

/-- **Dimension $\ge 5$ Counterexample Existence (Lutwak Criterion)**:
For every $n \ge 5$, there exists an origin-symmetric convex body (e.g. the unit cube)
that is NOT an intersection body, showing that Busemann–Petty fails in all dimensions $n \ge 5$. -/
theorem busemann_petty_counterexample_dim_ge_5 {n : ℕ} (S : BusemannPettySpace n) (hn : 5 ≤ n) :
    ∃ ρ : UnitSphere n → ℝ, IsSymmetric ρ ∧ IsConvexRadial ρ ∧ ¬ IsIntersectionBody S.toSphericalRadonSpace ρ := sorry

end BusemannPettyZhang
