import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace HedetniemiCounterexample

open SimpleGraph

/-!
# Tensor Product of Simple Graphs & Canonical Bounds
-/

/-- Categorical (tensor) product of simple graphs `G` and `H`.
Vertices are pairs `(u, v)` and edges connect `(u₁, v₁)` and `(u₂, v₂)`
iff `G.Adj u₁ u₂` and `H.Adj v₁ v₂`. -/
def tensorProduct {V₁ V₂ : Type*} (G : SimpleGraph V₁) (H : SimpleGraph V₂) : SimpleGraph (V₁ × V₂) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun {_ _} h ↦ ⟨G.adj_symm h.1, H.adj_symm h.2⟩⟩
  loopless := ⟨fun _ h ↦ G.irrefl h.1⟩

@[simp]
theorem tensorProduct_adj {V₁ V₂ : Type*} (G : SimpleGraph V₁) (H : SimpleGraph V₂)
    (x y : V₁ × V₂) :
    (tensorProduct G H).Adj x y ↔ G.Adj x.1 y.1 ∧ H.Adj x.2 y.2 :=
  Iff.rfl

/-- Projection homomorphism from `tensorProduct G H` to the first factor `G`. -/
def tensorProduct_fst {V₁ V₂ : Type*} (G : SimpleGraph V₁) (H : SimpleGraph V₂) :
    (tensorProduct G H) →g G where
  toFun := Prod.fst
  map_rel' h := h.1

/-- Projection homomorphism from `tensorProduct G H` to the second factor `H`. -/
def tensorProduct_snd {V₁ V₂ : Type*} (G : SimpleGraph V₁) (H : SimpleGraph V₂) :
    (tensorProduct G H) →g H where
  toFun := Prod.snd
  map_rel' h := h.2

/-- A graph homomorphism `G →g G'` weakly decreases chromatic number. -/
theorem chromaticNumber_le_of_hom {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}
    (f : G →g G') : G.chromaticNumber ≤ G'.chromaticNumber := sorry

/-- The chromatic number of `tensorProduct G H` is bounded above by `G.chromaticNumber`. -/
theorem chromaticNumber_tensorProduct_le_left {V₁ V₂ : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂) :
    (tensorProduct G H).chromaticNumber ≤ G.chromaticNumber := sorry

/-- The chromatic number of `tensorProduct G H` is bounded above by `H.chromaticNumber`. -/
theorem chromaticNumber_tensorProduct_le_right {V₁ V₂ : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂) :
    (tensorProduct G H).chromaticNumber ≤ H.chromaticNumber := sorry

/-- Canonical upper bound for Hedetniemi's conjecture:
`χ(G × H) ≤ min(χ(G), χ(H))`. -/
theorem chromaticNumber_tensorProduct_le_min {V₁ V₂ : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂) :
    (tensorProduct G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber := sorry

/-- If `G` is $n$-colorable, then `tensorProduct G H` is $n$-colorable. -/
theorem colorable_tensorProduct_of_left {V₁ V₂ : Type*} (G : SimpleGraph V₁) (H : SimpleGraph V₂)
    {n : ℕ} (hG : G.Colorable n) : (tensorProduct G H).Colorable n := sorry

/-- If `H` is $n$-colorable, then `tensorProduct G H` is $n$-colorable. -/
theorem colorable_tensorProduct_of_right {V₁ V₂ : Type*} (G : SimpleGraph V₁) (H : SimpleGraph V₂)
    {n : ℕ} (hH : H.Colorable n) : (tensorProduct G H).Colorable n := sorry

/-!
# Exponential Graph & Canonical Evaluation Coloring
-/

/-- The exponential graph $\mathcal{E}_c(\Gamma)$ (El-Zahar & Sauer 1985; Shitov 2019):
vertices are colorings $f : V \to \text{Fin } c$, and two distinct colorings $f \ne g$
are adjacent iff for all edges $u \sim v$ in $\Gamma$, $f(u) \ne g(v)$. -/
def exponentialGraph {V : Type*} (Γ : SimpleGraph V) (c : ℕ) : SimpleGraph (V → Fin c) where
  Adj f g := f ≠ g ∧ ∀ ⦃u v : V⦄, Γ.Adj u v → f u ≠ g v
  symm := ⟨fun {_ _} h ↦ ⟨h.1.symm, fun {_u _v} huv h_eq ↦ h.2 (Γ.adj_symm huv) h_eq.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

@[simp]
theorem exponentialGraph_adj {V : Type*} (Γ : SimpleGraph V) (c : ℕ) (f g : V → Fin c) :
    (exponentialGraph Γ c).Adj f g ↔ f ≠ g ∧ ∀ ⦃u v : V⦄, Γ.Adj u v → f u ≠ g v :=
  Iff.rfl

/-- The canonical evaluation map $E(v, f) = f(v)$ defines a proper $c$-coloring
of $\Gamma \times \mathcal{E}_c(\Gamma)$. -/
def evaluationColoring {V : Type*} (Γ : SimpleGraph V) (c : ℕ) :
    (tensorProduct Γ (exponentialGraph Γ c)).Coloring (Fin c) where
  toFun x := x.2 x.1
  map_rel' {x y} h := by
    have hadj_Γ := h.1
    have hadj_exp := h.2
    exact hadj_exp.2 hadj_Γ

/-- The tensor product $\Gamma \times \mathcal{E}_c(\Gamma)$ is always $c$-colorable. -/
theorem colorable_exponentialProduct {V : Type*} (Γ : SimpleGraph V) (c : ℕ) :
    (tensorProduct Γ (exponentialGraph Γ c)).Colorable c := sorry

/-!
# Shitov's Structural Disproof of Hedetniemi's Conjecture
-/

/-- A Shitov counterexample configuration for Hedetniemi's conjecture:
two graphs $G, H$ whose product is $c$-colorable, but neither factor is $c$-colorable. -/
structure ShitovPair where
  {V₁ V₂ : Type}
  [fintype₁ : Fintype V₁]
  [fintype₂ : Fintype V₂]
  G : SimpleGraph V₁
  H : SimpleGraph V₂
  c : ℕ
  colorable_product : (tensorProduct G H).Colorable c
  not_colorable_left : ¬ G.Colorable c
  not_colorable_right : ¬ H.Colorable c

/-- Any Shitov pair yields a strict inequality in Hedetniemi's product formula:
$\chi(G \times H) < \min(\chi(G), \chi(H))$. -/
theorem shitov_pair_strict_inequality (p : ShitovPair) :
    (tensorProduct p.G p.H).chromaticNumber < min p.G.chromaticNumber p.H.chromaticNumber := sorry

/-- Main Theorem: Hedetniemi's conjecture is false.
Given a Shitov counterexample pair, the conjecture fails. -/
theorem not_hedetniemi_conjecture (p : ShitovPair) :
    ¬ (∀ (V₁ V₂ : Type) [Fintype V₁] [Fintype V₂] (G : SimpleGraph V₁) (H : SimpleGraph V₂),
        (tensorProduct G H).chromaticNumber = min G.chromaticNumber H.chromaticNumber) := sorry

end HedetniemiCounterexample
