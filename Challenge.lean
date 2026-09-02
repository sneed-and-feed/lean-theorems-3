import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false

namespace JenrichBorsuk64

open scoped Classical

/-!
# Metric & Combinatorial Foundations of Borsuk's Conjecture
-/

section MetricFoundations

variable {α : Type*} [PseudoMetricSpace α]

/-- A Borsuk cover of a set `S` is a finite collection of sets covering `S`,
each having strictly smaller diameter than `S`. -/
def IsBorsukCover (S : Set α) (C : Finset (Set α)) : Prop :=
  (S ⊆ ⋃ c ∈ C, c) ∧ ∀ c ∈ C, Metric.diam c < Metric.diam S

/-- Borsuk's conjecture in dimension `n`: every bounded set in `ℝⁿ` with positive diameter
can be covered by at most `n + 1` sets of strictly smaller diameter. -/
def BorsukConjecture (n : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin n))), Bornology.IsBounded S → 0 < Metric.diam S →
    ∃ C : Finset (Set (EuclideanSpace ℝ (Fin n))), C.card ≤ n + 1 ∧ IsBorsukCover S C

/-- A two-distance set in a metric space is a set where the distance between any two
distinct points takes one of two positive values `d₁ < d₂`. -/
def IsTwoDistanceSet (S : Set α) (d₁ d₂ : ℝ) : Prop :=
  0 < d₁ ∧ d₁ < d₂ ∧ ∀ ⦃u v⦄, u ∈ S → v ∈ S → u ≠ v → dist u v = d₁ ∨ dist u v = d₂

/-- The distance-`d₁` graph on a subset `S` of a metric space. -/
def distanceGraph (S : Set α) (d₁ : ℝ) : SimpleGraph S where
  Adj u v := u ≠ v ∧ dist (u : α) (v : α) = d₁
  symm := ⟨fun {u v} h => ⟨h.1.symm, by rw [dist_comm, h.2]⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- Fundamental clique-diameter lemma: in any two-distance set `S` with distances `d₁ < d₂`,
any bounded subset `U ⊆ S` of diameter `< d₂` cannot contain two points at distance `d₂`,
hence all distinct pairs in `U` are at distance `d₁`. -/
theorem dist_eq_d1_of_diam_lt {S : Set α} {d₁ d₂ : ℝ}
    (h2d : IsTwoDistanceSet S d₁ d₂) {U : Set α} (hU : Bornology.IsBounded U) (hUS : U ⊆ S)
    (hdiam : Metric.diam U < d₂) {u v : α} (hu : u ∈ U) (hv : v ∈ U) (hne : u ≠ v) :
    dist u v = d₁ := sorry

/-- In any two-distance set `S`, any bounded subset `U ⊆ S` of diameter `< d₂`
induces a clique in the distance-`d₁` graph. -/
theorem isClique_of_diam_lt {S : Set α} {d₁ d₂ : ℝ}
    (h2d : IsTwoDistanceSet S d₁ d₂) {U : Set α} (hU : Bornology.IsBounded U) (hUS : U ⊆ S)
    (hdiam : Metric.diam U < d₂) :
    ∀ ⦃u v : S⦄, (u : α) ∈ U → (v : α) ∈ U → u ≠ v →
      (distanceGraph S d₁).Adj u v := sorry

end MetricFoundations

section PigeonholeBound

variable {α : Type*}

/-- Pigeonhole partition bound: if a finite set `S` is covered by a family of sets `C`,
and each piece `c ∈ C` contains at most `m` elements of `S`, then `|S| ≤ |C| * m`. -/
theorem card_le_mul_card_cover (S : Finset α) (C : Finset (Set α))
    (h_cov : (S : Set α) ⊆ ⋃ c ∈ C, c) {m : ℕ}
    (h_part : ∀ c ∈ C, (S.filter (· ∈ c)).card ≤ m) :
    S.card ≤ C.card * m := sorry

/-- If `|S| > k * m`, then no cover of `S` by `k` sets can have all pieces of size `≤ m`. -/
theorem no_small_cover_of_card_gt (S : Finset α) (C : Finset (Set α))
    (h_cov : (S : Set α) ⊆ ⋃ c ∈ C, c) {m : ℕ}
    (h_part : ∀ c ∈ C, (S.filter (· ∈ c)).card ≤ m)
    {k : ℕ} (hk : C.card ≤ k) (h_gt : k * m < S.card) : False := sorry

end PigeonholeBound

/-!
# Euclidean Representation of Strongly Regular Graphs & G₂(4)
-/

section SRGParameters

/-- Strongly regular graph parameters `(v, k, lam, μ)` and its spectral decomposition
with eigenvalues `k` (multiplicity 1), `r > 0` (multiplicity `f`), and `s < 0` (multiplicity `g`). -/
structure SRGParameters where
  v : ℕ
  k : ℕ
  lam : ℕ
  μ : ℕ
  r : ℝ
  s : ℝ
  f : ℕ
  g : ℕ
  h_v : v = 1 + f + g
  h_trace : (k : ℝ) + (f : ℝ) * r + (g : ℝ) * s = 0
  h_spectral : (r - s) ^ 2 = ((lam : ℝ) - (μ : ℝ)) ^ 2 + 4 * ((k : ℝ) - (μ : ℝ))
  h_quad_sum : r + s = (lam : ℝ) - (μ : ℝ)
  h_quad_prod : r * s = -((k : ℝ) - (μ : ℝ))
  h_k_spec : ((k : ℝ) - r) * ((k : ℝ) - s) = (μ : ℝ) * (v : ℝ)

/-- Parameters of the Suzuki strongly regular graph `G₂(4) = srg(416, 100, 36, 20)`. -/
def g2_4_params : SRGParameters where
  v := 416
  k := 100
  lam := 36
  μ := 20
  r := 20
  s := -4
  f := 65
  g := 350
  h_v := by decide
  h_trace := by norm_num
  h_spectral := by norm_num
  h_quad_sum := by norm_num
  h_quad_prod := by norm_num
  h_k_spec := by norm_num

/-- Bondarenko's partition lower bound in 65 dimensions: `416 / 5 = 83.2`, so any partition
into cliques requires at least `84` parts, which strictly exceeds `65 + 1 = 66`. -/
theorem bondarenko_bound_65 : (416 + 5 - 1) / 5 = 84 := sorry

theorem bondarenko_exceeds_65 : 84 > 65 + 1 := sorry

end SRGParameters

section EuclideanRepresentation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The shifted adjacency matrix `Y = A - sI = A + 4I`. -/
def Y (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  (if G.Adj i j then 1 else 0) + (if i = j then 4 else 0)

theorem Y_diag (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    Y G i i = 4 := sorry

theorem Y_of_adj (G : SimpleGraph V) [DecidableRel G.Adj] {i j : V} (h : G.Adj i j) :
    Y G i j = 1 := sorry

theorem Y_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj] {i j : V} (hne : i ≠ j) (hnadj : ¬ G.Adj i j) :
    Y G i j = 0 := sorry

theorem Y_symm (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    Y G i j = Y G j i := sorry

/-- Euclidean representation vectors `y i : EuclideanSpace ℝ V`. -/
def y (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun j => Y G i j)

/-- The row sum of `Y` over any subset `B` counts the neighbors in `B` plus `4` if `i ∈ B`. -/
theorem sum_Y_eq_neighbors_add (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (i : V) :
    ∑ j ∈ B, Y G i j = ((G.neighborFinset i ∩ B).card : ℝ) + (if i ∈ B then 4 else 0) := sorry

theorem dist_sq_eq_inner_sub_two_mul_add (u v : EuclideanSpace ℝ V) :
    dist u v ^ 2 = @inner ℝ (EuclideanSpace ℝ V) _ u u - 2 * @inner ℝ (EuclideanSpace ℝ V) _ u v +
      @inner ℝ (EuclideanSpace ℝ V) _ v v := sorry

/-- When the Gram matrix of vectors `y i` is `20 + 24 * Y`, adjacent vertices have squared distance 144. -/
theorem dist_sq_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_gram : ∀ i j, @inner ℝ (EuclideanSpace ℝ V) _ (y G i) (y G j) = 20 + 24 * Y G i j)
    (i j : V) (hadj : G.Adj i j) :
    dist (y G i) (y G j) ^ 2 = 144 := sorry

/-- When the Gram matrix of vectors `y i` is `20 + 24 * Y`, non-adjacent distinct vertices
have squared distance 192. -/
theorem dist_sq_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_gram : ∀ i j, @inner ℝ (EuclideanSpace ℝ V) _ (y G i) (y G j) = 20 + 24 * Y G i j)
    (i j : V) (hne : i ≠ j) (hnadj : ¬ G.Adj i j) :
    dist (y G i) (y G j) ^ 2 = 192 := sorry

/-- Centered vectors `z i = y i - y_bar`. -/
def z (G : SimpleGraph V) [DecidableRel G.Adj] (y_bar : EuclideanSpace ℝ V) (i : V) :
    EuclideanSpace ℝ V :=
  y G i - y_bar

/-- Centering preserves pairwise Euclidean distances. -/
theorem dist_z_eq_dist_y (G : SimpleGraph V) [DecidableRel G.Adj]
    (y_bar : EuclideanSpace ℝ V) (i j : V) :
    dist (z G y_bar i) (z G y_bar j) = dist (y G i) (y G j) := sorry

end EuclideanRepresentation

/-!
# Jenrich's 64-Dimensional Reduction Vector
-/

section JenrichReduction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Jenrich partition structure on a 416-vertex strongly regular graph:
the vertex set is partitioned into three disjoint 32-sets `B₁, B₂, B₃` and a 320-set `C`,
with exact cross-incidence regularities. -/
structure JenrichPartition (G : SimpleGraph V) [DecidableRel G.Adj] where
  B₁ : Finset V
  B₂ : Finset V
  B₃ : Finset V
  C : Finset V
  card_V : Fintype.card V = 416
  card_B₁ : B₁.card = 32
  card_B₂ : B₂.card = 32
  card_B₃ : B₃.card = 32
  card_C : C.card = 320
  disj_12 : Disjoint B₁ B₂
  disj_13 : Disjoint B₁ B₃
  disj_23 : Disjoint B₂ B₃
  disj_1C : Disjoint B₁ C
  disj_2C : Disjoint B₂ C
  disj_3C : Disjoint B₃ C
  union_eq : B₁ ∪ B₂ ∪ B₃ ∪ C = Finset.univ
  -- Incidence counts
  deg_B1_self : ∀ i ∈ B₁, (G.neighborFinset i ∩ B₁).card = 20
  deg_B2_self : ∀ i ∈ B₂, (G.neighborFinset i ∩ B₂).card = 20
  deg_B3_self : ∀ i ∈ B₃, (G.neighborFinset i ∩ B₃).card = 20
  deg_B1_of_B2 : ∀ i ∈ B₂, (G.neighborFinset i ∩ B₁).card = 0
  deg_B1_of_B3 : ∀ i ∈ B₃, (G.neighborFinset i ∩ B₁).card = 0
  deg_B2_of_B1 : ∀ i ∈ B₁, (G.neighborFinset i ∩ B₂).card = 0
  deg_B2_of_B3 : ∀ i ∈ B₃, (G.neighborFinset i ∩ B₂).card = 0
  deg_B3_of_B1 : ∀ i ∈ B₁, (G.neighborFinset i ∩ B₃).card = 0
  deg_B3_of_B2 : ∀ i ∈ B₂, (G.neighborFinset i ∩ B₃).card = 0
  deg_B1_C : ∀ i ∈ C, (G.neighborFinset i ∩ B₁).card = 8
  deg_B2_C : ∀ i ∈ C, (G.neighborFinset i ∩ B₂).card = 8
  deg_B3_C : ∀ i ∈ C, (G.neighborFinset i ∩ B₃).card = 8
  clique_free_6 : G.CliqueFree 6

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The carrier set `S₆₄ = C ∪ B₁` has cardinality 352. -/
theorem carrier_card_eq (jp : JenrichPartition G) : (jp.C ∪ jp.B₁).card = 352 := sorry

/-- Row sum on `B_h` for `i ∈ B_h` is 24. -/
theorem row_sum_self (_jp : JenrichPartition G) {B : Finset V} (i : V) (hi : i ∈ B)
    (h_deg : (G.neighborFinset i ∩ B).card = 20) :
    ∑ j ∈ B, Y G i j = 24 := sorry

/-- Row sum on `B_h` for `i` with 0 neighbors in `B_h` and `i ∉ B_h` is 0. -/
theorem row_sum_zero (_jp : JenrichPartition G) {B : Finset V} (i : V) (hi : i ∉ B)
    (h_deg : (G.neighborFinset i ∩ B).card = 0) :
    ∑ j ∈ B, Y G i j = 0 := sorry

/-- Row sum on `B_h` for `i ∈ C` is 8. -/
theorem row_sum_C (_jp : JenrichPartition G) {B : Finset V} (i : V) (hi : i ∉ B)
    (h_deg : (G.neighborFinset i ∩ B).card = 8) :
    ∑ j ∈ B, Y G i j = 8 := sorry

/-- Jenrich's reduction vector `p = 1_{B₂} - 1_{B₃}`. -/
def p (jp : JenrichPartition G) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun j => (if j ∈ jp.B₂ then (1 : ℝ) else 0) - (if j ∈ jp.B₃ then 1 else 0))

theorem sum_mul_indicator (f : V → ℝ) (B : Finset V) :
    (∑ x, f x * (if x ∈ B then (1 : ℝ) else 0)) = ∑ x ∈ B, f x := sorry

/-- Expansion of the inner product `⟨p, y i⟩` into row sums over `B₂` and `B₃`. -/
theorem inner_p_y_eq (jp : JenrichPartition G) (i : V) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = ∑ j ∈ jp.B₂, Y G i j - ∑ j ∈ jp.B₃, Y G i j := sorry

/-- Jenrich's reduction vector `p` is orthogonal to `y i` for every vertex `i ∈ C`. -/
theorem reduction_vector_ortho_C (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.C) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = 0 := sorry

/-- Jenrich's reduction vector `p` is orthogonal to `y i` for every vertex `i ∈ B₁`. -/
theorem reduction_vector_ortho_B1 (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.B₁) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = 0 := sorry

/-- Jenrich's orthogonality theorem: `p` is orthogonal to `y i` for every vertex
in the 64-dimensional carrier `S₆₄ = C ∪ B₁`. -/
theorem reduction_vector_ortho_carrier (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.C ∪ jp.B₁) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = 0 := sorry

/-- On the other hand, `p` is NOT orthogonal to vectors in `B₂`: `⟨p, y j⟩ = 24 ≠ 0`. -/
theorem reduction_vector_nonortho_B2 (jp : JenrichPartition G) (j : V) (hj : j ∈ jp.B₂) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G j) = 24 := sorry

/-- The reduction vector `p` is orthogonal to the all-ones vector `1`. -/
theorem inner_p_ones_eq_zero (jp : JenrichPartition G) :
    (∑ j : V, (p jp j)) = 0 := sorry

/-- The all-ones vector in `EuclideanSpace ℝ V`. -/
def ones (V : Type*) [Fintype V] : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun _ => 1)

/-- Inner product of `p` with the all-ones vector is 0. -/
theorem inner_p_ones (jp : JenrichPartition G) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (ones V) = 0 := sorry

/-- Inner product of `p` with any constant multiple of the all-ones vector is 0. -/
theorem inner_p_smul_ones (jp : JenrichPartition G) (c : ℝ) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (c • ones V) = 0 := sorry

/-- For centered vectors `z i = y i - c • 1`, `p` is orthogonal to `z i`
for all `i` in the carrier set `S₆₄ = C ∪ B₁`. -/
theorem inner_p_z_carrier (jp : JenrichPartition G) (c : ℝ) (i : V)
    (hi : i ∈ jp.C ∪ jp.B₁) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (z G (c • ones V) i) = 0 := sorry

/-- But `p` is not orthogonal to `z j` for `j ∈ B₂`: `⟨p, z j⟩ = 24 ≠ 0`. -/
theorem inner_p_z_nonortho_B2 (jp : JenrichPartition G) (c : ℝ) (j : V)
    (hj : j ∈ jp.B₂) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (z G (c • ones V) j) = 24 := sorry

/-- Lower bound on parts required to cover `S₆₄`: any smaller-diameter cover
requires at least 71 parts. -/
theorem jenrich_bound_64 : (352 + 5 - 1) / 5 = 71 := sorry

theorem jenrich_exceeds_64 : 71 > 64 + 1 := sorry

theorem jenrich_partition_lower_bound (jp : JenrichPartition G)
    (C_parts : Finset (Set V)) (h_cov : ((jp.C ∪ jp.B₁ : Finset V) : Set V) ⊆ ⋃ c ∈ C_parts, c)
    (h_clique : ∀ c ∈ C_parts, ((jp.C ∪ jp.B₁).filter (· ∈ c)).card ≤ 5) :
    71 ≤ C_parts.card := sorry

/-- Main Theorem: Borsuk's conjecture is FALSE in dimension 64.
Given a bounded set `S ⊆ ℝ⁶⁴` of positive diameter whose subsets of smaller diameter
require at least 71 covering sets, Borsuk's conjecture fails. -/
theorem not_borsuk_conjecture_64
    {S : Set (EuclideanSpace ℝ (Fin 64))}
    (h_bdd : Bornology.IsBounded S)
    (h_pos : 0 < Metric.diam S)
    (h_bound : ∀ C : Finset (Set (EuclideanSpace ℝ (Fin 64))), IsBorsukCover S C → 71 ≤ C.card) :
    ¬ BorsukConjecture 64 := sorry

end JenrichReduction

/-!
# Jenrich's 63-Dimensional Almost-Counterexample
-/

section Jenrich63

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Secondary reduction vector `q = 2 * 1_{B₁} - 1_{B₂} - 1_{B₃}`. -/
def q (jp : JenrichPartition G) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun j => 2 * (if j ∈ jp.B₁ then (1 : ℝ) else 0) -
    (if j ∈ jp.B₂ then 1 else 0) - (if j ∈ jp.B₃ then 1 else 0))

/-- Expansion of the inner product `⟨q, y i⟩` into row sums over `B₁, B₂, B₃`. -/
theorem inner_q_y_eq (jp : JenrichPartition G) (i : V) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G i) =
      2 * (∑ j ∈ jp.B₁, Y G i j) - (∑ j ∈ jp.B₂, Y G i j) - (∑ j ∈ jp.B₃, Y G i j) := sorry

/-- The vector `q` is orthogonal to `y i` for every vertex `i ∈ C`. -/
theorem reduction_vector_q_ortho_C (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.C) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G i) = 0 := sorry

/-- Sum of entries of `q` is zero: `2 * 32 - 32 - 32 = 0`. -/
theorem inner_q_ones_eq_zero (jp : JenrichPartition G) :
    (∑ j : V, (q jp j)) = 0 := sorry

/-- Inner product of `q` with the all-ones vector is 0. -/
theorem inner_q_ones (jp : JenrichPartition G) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (ones V) = 0 := sorry

/-- Inner product of `q` with any constant multiple of the all-ones vector is 0. -/
theorem inner_q_smul_ones (jp : JenrichPartition G) (c : ℝ) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (c • ones V) = 0 := sorry

/-- The vector `q` is orthogonal to `z i` for all `i ∈ C`. -/
theorem inner_q_z_C (jp : JenrichPartition G) (c : ℝ) (i : V) (hi : i ∈ jp.C) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (z G (c • ones V) i) = 0 := sorry

/-- The 63-dimensional almost-counterexample bound: `320 / 5 = 64 = 63 + 1`.
The 320-point set `C` achieves the Borsuk partition number in dimension 63. -/
theorem jenrich_bound_63 : 320 / 5 = 64 := sorry

theorem jenrich_achieves_63 : 64 = 63 + 1 := sorry

/-- Any smaller-diameter cover of `C` requires at least 64 parts. -/
theorem almost_counterexample_63 (jp : JenrichPartition G)
    (C_parts : Finset (Set V)) (h_cov : (jp.C : Set V) ⊆ ⋃ c ∈ C_parts, c)
    (h_clique : ∀ c ∈ C_parts, (jp.C.filter (· ∈ c)).card ≤ 5) :
    64 ≤ C_parts.card := sorry

end Jenrich63

end JenrichBorsuk64
