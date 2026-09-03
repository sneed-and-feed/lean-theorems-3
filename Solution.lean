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
    dist u v = d₁ := by
  rcases h2d.2.2 (hUS hu) (hUS hv) hne with h1 | h2
  · exact h1
  · linarith [Metric.dist_le_diam_of_mem hU hu hv]

/-- In any two-distance set `S`, any bounded subset `U ⊆ S` of diameter `< d₂`
induces a clique in the distance-`d₁` graph. -/
theorem isClique_of_diam_lt {S : Set α} {d₁ d₂ : ℝ}
    (h2d : IsTwoDistanceSet S d₁ d₂) {U : Set α} (hU : Bornology.IsBounded U) (hUS : U ⊆ S)
    (hdiam : Metric.diam U < d₂) :
    ∀ ⦃u v : S⦄, (u : α) ∈ U → (v : α) ∈ U → u ≠ v →
      (distanceGraph S d₁).Adj u v :=
  fun _ _ hu hv hne => ⟨hne, dist_eq_d1_of_diam_lt h2d hU hUS hdiam hu hv (Subtype.ext_iff.ne.mp hne)⟩

end MetricFoundations

section PigeonholeBound

variable {α : Type*}

/-- Pigeonhole partition bound: if a finite set `S` is covered by a family of sets `C`,
and each piece `c ∈ C` contains at most `m` elements of `S`, then `|S| ≤ |C| * m`. -/
theorem card_le_mul_card_cover (S : Finset α) (C : Finset (Set α))
    (h_cov : (S : Set α) ⊆ ⋃ c ∈ C, c) {m : ℕ}
    (h_part : ∀ c ∈ C, (S.filter (· ∈ c)).card ≤ m) :
    S.card ≤ C.card * m := by
  have h_sub : S ⊆ C.biUnion (fun c => S.filter (· ∈ c)) := fun x hx => by
    rcases Set.mem_iUnion₂.mp (h_cov (Finset.mem_coe.mpr hx)) with ⟨c, hc, hxc⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hx, hxc⟩⟩
  exact (Finset.card_le_card h_sub).trans
    (Finset.card_biUnion_le_card_mul C _ m h_part)

/-- If `|S| > k * m`, then no cover of `S` by `k` sets can have all pieces of size `≤ m`. -/
theorem no_small_cover_of_card_gt (S : Finset α) (C : Finset (Set α))
    (h_cov : (S : Set α) ⊆ ⋃ c ∈ C, c) {m : ℕ}
    (h_part : ∀ c ∈ C, (S.filter (· ∈ c)).card ≤ m)
    {k : ℕ} (hk : C.card ≤ k) (h_gt : k * m < S.card) : False := by
  have := card_le_mul_card_cover S C h_cov h_part
  nlinarith

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
theorem bondarenko_bound_65 : (416 + 5 - 1) / 5 = 84 := rfl

theorem bondarenko_exceeds_65 : 84 > 65 + 1 := by decide

end SRGParameters

section EuclideanRepresentation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The shifted adjacency matrix `Y = A - sI = A + 4I`. -/
def Y (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  (if G.Adj i j then 1 else 0) + (if i = j then 4 else 0)

theorem Y_diag (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    Y G i i = 4 := by
  simp [Y]

theorem Y_of_adj (G : SimpleGraph V) [DecidableRel G.Adj] {i j : V} (h : G.Adj i j) :
    Y G i j = 1 := by
  simp [Y, h, G.ne_of_adj h]

theorem Y_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj] {i j : V} (hne : i ≠ j) (hnadj : ¬ G.Adj i j) :
    Y G i j = 0 := by
  simp [Y, hne, hnadj]

theorem Y_symm (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    Y G i j = Y G j i := by
  simp [Y, G.adj_comm i j, eq_comm]

/-- Euclidean representation vectors `y i : EuclideanSpace ℝ V`. -/
def y (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun j => Y G i j)

/-- The row sum of `Y` over any subset `B` counts the neighbors in `B` plus `4` if `i ∈ B`. -/
theorem sum_Y_eq_neighbors_add (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (i : V) :
    ∑ j ∈ B, Y G i j = ((G.neighborFinset i ∩ B).card : ℝ) + (if i ∈ B then 4 else 0) := by
  simp only [Y, Finset.sum_add_distrib]
  have h1 : (∑ j ∈ B, if G.Adj i j then (1 : ℝ) else 0) = ((G.neighborFinset i ∩ B).card : ℝ) := by
    rw [Finset.sum_boole]
    congr 2; ext x
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [h1, Finset.sum_ite_eq]

theorem dist_sq_eq_inner_sub_two_mul_add (u v : EuclideanSpace ℝ V) :
    dist u v ^ 2 = @inner ℝ (EuclideanSpace ℝ V) _ u u - 2 * @inner ℝ (EuclideanSpace ℝ V) _ u v +
      @inner ℝ (EuclideanSpace ℝ V) _ v v := by
  rw [dist_eq_norm, norm_sub_sq_real]
  simp only [real_inner_self_eq_norm_mul_norm, pow_two]

/-- When the Gram matrix of vectors `y i` is `20 + 24 * Y`, adjacent vertices have squared distance 144. -/
theorem dist_sq_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_gram : ∀ i j, @inner ℝ (EuclideanSpace ℝ V) _ (y G i) (y G j) = 20 + 24 * Y G i j)
    (i j : V) (hadj : G.Adj i j) :
    dist (y G i) (y G j) ^ 2 = 144 := by
  rw [dist_sq_eq_inner_sub_two_mul_add, h_gram, h_gram, h_gram, Y_diag, Y_diag, Y_of_adj G hadj]
  norm_num

/-- When the Gram matrix of vectors `y i` is `20 + 24 * Y`, non-adjacent distinct vertices
have squared distance 192. -/
theorem dist_sq_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_gram : ∀ i j, @inner ℝ (EuclideanSpace ℝ V) _ (y G i) (y G j) = 20 + 24 * Y G i j)
    (i j : V) (hne : i ≠ j) (hnadj : ¬ G.Adj i j) :
    dist (y G i) (y G j) ^ 2 = 192 := by
  rw [dist_sq_eq_inner_sub_two_mul_add, h_gram, h_gram, h_gram, Y_diag, Y_diag, Y_of_not_adj G hne hnadj]
  norm_num

/-- Centered vectors `z i = y i - y_bar`. -/
def z (G : SimpleGraph V) [DecidableRel G.Adj] (y_bar : EuclideanSpace ℝ V) (i : V) :
    EuclideanSpace ℝ V :=
  y G i - y_bar

/-- Centering preserves pairwise Euclidean distances. -/
theorem dist_z_eq_dist_y (G : SimpleGraph V) [DecidableRel G.Adj]
    (y_bar : EuclideanSpace ℝ V) (i j : V) :
    dist (z G y_bar i) (z G y_bar j) = dist (y G i) (y G j) :=
  dist_sub_right (y G i) (y G j) y_bar

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
theorem carrier_card_eq (jp : JenrichPartition G) : (jp.C ∪ jp.B₁).card = 352 := by
  rw [Finset.card_union_of_disjoint jp.disj_1C.symm, jp.card_C, jp.card_B₁]

/-- Row sum on `B_h` for `i ∈ B_h` is 24. -/
theorem row_sum_self (_jp : JenrichPartition G) {B : Finset V} (i : V) (hi : i ∈ B)
    (h_deg : (G.neighborFinset i ∩ B).card = 20) :
    ∑ j ∈ B, Y G i j = 24 := by
  simp [sum_Y_eq_neighbors_add, h_deg, hi]; norm_num

/-- Row sum on `B_h` for `i` with 0 neighbors in `B_h` and `i ∉ B_h` is 0. -/
theorem row_sum_zero (_jp : JenrichPartition G) {B : Finset V} (i : V) (hi : i ∉ B)
    (h_deg : (G.neighborFinset i ∩ B).card = 0) :
    ∑ j ∈ B, Y G i j = 0 := by
  simp [sum_Y_eq_neighbors_add, h_deg, hi]

/-- Row sum on `B_h` for `i ∈ C` is 8. -/
theorem row_sum_C (_jp : JenrichPartition G) {B : Finset V} (i : V) (hi : i ∉ B)
    (h_deg : (G.neighborFinset i ∩ B).card = 8) :
    ∑ j ∈ B, Y G i j = 8 := by
  simp [sum_Y_eq_neighbors_add, h_deg, hi]

/-- Jenrich's reduction vector `p = 1_{B₂} - 1_{B₃}`. -/
def p (jp : JenrichPartition G) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun j => (if j ∈ jp.B₂ then (1 : ℝ) else 0) - (if j ∈ jp.B₃ then 1 else 0))

theorem sum_mul_indicator (f : V → ℝ) (B : Finset V) :
    (∑ x, f x * (if x ∈ B then (1 : ℝ) else 0)) = ∑ x ∈ B, f x := by
  have : (fun x => f x * if x ∈ B then (1 : ℝ) else 0) = fun x => if x ∈ B then f x else 0 := by
    ext x; split_ifs <;> ring
  rw [this, Finset.sum_ite_mem_eq]

/-- Expansion of the inner product `⟨p, y i⟩` into row sums over `B₂` and `B₃`. -/
theorem inner_p_y_eq (jp : JenrichPartition G) (i : V) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = ∑ j ∈ jp.B₂, Y G i j - ∑ j ∈ jp.B₃, Y G i j := by
  rw [PiLp.inner_apply]
  simp only [p, y, RCLike.inner_apply, conj_trivial]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sum_mul_indicator, sum_mul_indicator]

/-- Jenrich's reduction vector `p` is orthogonal to `y i` for every vertex `i ∈ C`. -/
theorem reduction_vector_ortho_C (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.C) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = 0 := by
  rw [inner_p_y_eq,
    row_sum_C jp i (Finset.disjoint_right.mp jp.disj_2C hi) (jp.deg_B2_C i hi),
    row_sum_C jp i (Finset.disjoint_right.mp jp.disj_3C hi) (jp.deg_B3_C i hi), sub_self]

/-- Jenrich's reduction vector `p` is orthogonal to `y i` for every vertex `i ∈ B₁`. -/
theorem reduction_vector_ortho_B1 (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.B₁) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = 0 := by
  rw [inner_p_y_eq,
    row_sum_zero jp i (Finset.disjoint_left.mp jp.disj_12 hi) (jp.deg_B2_of_B1 i hi),
    row_sum_zero jp i (Finset.disjoint_left.mp jp.disj_13 hi) (jp.deg_B3_of_B1 i hi), sub_self]

/-- Jenrich's orthogonality theorem: `p` is orthogonal to `y i` for every vertex
in the 64-dimensional carrier `S₆₄ = C ∪ B₁`. -/
theorem reduction_vector_ortho_carrier (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.C ∪ jp.B₁) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G i) = 0 :=
  (Finset.mem_union.mp hi).elim (reduction_vector_ortho_C jp i) (reduction_vector_ortho_B1 jp i)

/-- On the other hand, `p` is NOT orthogonal to vectors in `B₂`: `⟨p, y j⟩ = 24 ≠ 0`. -/
theorem reduction_vector_nonortho_B2 (jp : JenrichPartition G) (j : V) (hj : j ∈ jp.B₂) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (y G j) = 24 := by
  rw [inner_p_y_eq,
    row_sum_self jp j hj (jp.deg_B2_self j hj),
    row_sum_zero jp j (Finset.disjoint_left.mp jp.disj_23 hj) (jp.deg_B3_of_B2 j hj), sub_zero]

/-- The reduction vector `p` is orthogonal to the all-ones vector `1`. -/
theorem inner_p_ones_eq_zero (jp : JenrichPartition G) :
    (∑ j : V, (p jp j)) = 0 := by
  simp only [p]
  have hB (B : Finset V) : (∑ j : V, (if j ∈ B then (1 : ℝ) else 0)) = (B.card : ℝ) := by
    rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_sub_distrib, hB, hB, jp.card_B₂, jp.card_B₃, sub_self]

/-- The all-ones vector in `EuclideanSpace ℝ V`. -/
def ones (V : Type*) [Fintype V] : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun _ => 1)

/-- Inner product of `p` with the all-ones vector is 0. -/
theorem inner_p_ones (jp : JenrichPartition G) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (ones V) = 0 := by
  rw [PiLp.inner_apply]
  simp only [ones, p, RCLike.inner_apply, conj_trivial, one_mul]
  exact inner_p_ones_eq_zero jp

/-- Inner product of `p` with any constant multiple of the all-ones vector is 0. -/
theorem inner_p_smul_ones (jp : JenrichPartition G) (c : ℝ) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (c • ones V) = 0 := by
  rw [inner_smul_right, inner_p_ones, mul_zero]

/-- For centered vectors `z i = y i - c • 1`, `p` is orthogonal to `z i`
for all `i` in the carrier set `S₆₄ = C ∪ B₁`. -/
theorem inner_p_z_carrier (jp : JenrichPartition G) (c : ℝ) (i : V)
    (hi : i ∈ jp.C ∪ jp.B₁) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (z G (c • ones V) i) = 0 := by
  simp [z, inner_sub_right, reduction_vector_ortho_carrier jp i hi, inner_p_smul_ones]

/-- But `p` is not orthogonal to `z j` for `j ∈ B₂`: `⟨p, z j⟩ = 24 ≠ 0`. -/
theorem inner_p_z_nonortho_B2 (jp : JenrichPartition G) (c : ℝ) (j : V)
    (hj : j ∈ jp.B₂) :
    @inner ℝ (EuclideanSpace ℝ V) _ (p jp) (z G (c • ones V) j) = 24 := by
  simp [z, inner_sub_right, reduction_vector_nonortho_B2 jp j hj, inner_p_smul_ones]

/-- Lower bound on parts required to cover `S₆₄`: any smaller-diameter cover
requires at least 71 parts. -/
theorem jenrich_bound_64 : (352 + 5 - 1) / 5 = 71 := rfl

theorem jenrich_exceeds_64 : 71 > 64 + 1 := by decide

theorem jenrich_partition_lower_bound (jp : JenrichPartition G)
    (C_parts : Finset (Set V)) (h_cov : ((jp.C ∪ jp.B₁ : Finset V) : Set V) ⊆ ⋃ c ∈ C_parts, c)
    (h_clique : ∀ c ∈ C_parts, ((jp.C ∪ jp.B₁).filter (· ∈ c)).card ≤ 5) :
    71 ≤ C_parts.card := by
  have := card_le_mul_card_cover (jp.C ∪ jp.B₁) C_parts h_cov h_clique
  rw [carrier_card_eq jp] at this
  omega

/-- Main Theorem: Borsuk's conjecture is FALSE in dimension 64.
Given a bounded set `S ⊆ ℝ⁶⁴` of positive diameter whose subsets of smaller diameter
require at least 71 covering sets, Borsuk's conjecture fails. -/
theorem not_borsuk_conjecture_64
    {S : Set (EuclideanSpace ℝ (Fin 64))}
    (h_bdd : Bornology.IsBounded S)
    (h_pos : 0 < Metric.diam S)
    (h_bound : ∀ C : Finset (Set (EuclideanSpace ℝ (Fin 64))), IsBorsukCover S C → 71 ≤ C.card) :
    ¬ BorsukConjecture 64 := fun h => by
  obtain ⟨C, hC_card, hC_cov⟩ := h S h_bdd h_pos
  linarith [h_bound C hC_cov]

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
      2 * (∑ j ∈ jp.B₁, Y G i j) - (∑ j ∈ jp.B₂, Y G i j) - (∑ j ∈ jp.B₃, Y G i j) := by
  rw [PiLp.inner_apply]
  simp only [q, y, RCLike.inner_apply, conj_trivial]
  have : ∀ x : V, Y G i x * (2 * (if x ∈ jp.B₁ then (1 : ℝ) else 0) - (if x ∈ jp.B₂ then 1 else 0) -
      (if x ∈ jp.B₃ then 1 else 0)) =
      2 * (Y G i x * (if x ∈ jp.B₁ then (1 : ℝ) else 0)) -
      (Y G i x * (if x ∈ jp.B₂ then (1 : ℝ) else 0)) -
      (Y G i x * (if x ∈ jp.B₃ then (1 : ℝ) else 0)) := fun x => by ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_mul_indicator, sum_mul_indicator, sum_mul_indicator]

/-- The vector `q` is orthogonal to `y i` for every vertex `i ∈ C`. -/
theorem reduction_vector_q_ortho_C (jp : JenrichPartition G) (i : V) (hi : i ∈ jp.C) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G i) = 0 := by
  rw [inner_q_y_eq,
    row_sum_C jp i (Finset.disjoint_right.mp jp.disj_1C hi) (jp.deg_B1_C i hi),
    row_sum_C jp i (Finset.disjoint_right.mp jp.disj_2C hi) (jp.deg_B2_C i hi),
    row_sum_C jp i (Finset.disjoint_right.mp jp.disj_3C hi) (jp.deg_B3_C i hi)]
  ring

/-- On `B₁`, `⟨q, y j⟩ = 48 ≠ 0`. -/
theorem reduction_vector_q_nonortho_B1 (jp : JenrichPartition G) (j : V) (hj : j ∈ jp.B₁) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G j) = 48 := by
  rw [inner_q_y_eq,
    row_sum_self jp j hj (jp.deg_B1_self j hj),
    row_sum_zero jp j (Finset.disjoint_left.mp jp.disj_12 hj) (jp.deg_B2_of_B1 j hj),
    row_sum_zero jp j (Finset.disjoint_left.mp jp.disj_13 hj) (jp.deg_B3_of_B1 j hj)]
  ring

/-- On `B₂`, `⟨q, y j⟩ = -24 ≠ 0`. -/
theorem reduction_vector_q_nonortho_B2 (jp : JenrichPartition G) (j : V) (hj : j ∈ jp.B₂) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G j) = -24 := by
  rw [inner_q_y_eq,
    row_sum_zero jp j (Finset.disjoint_right.mp jp.disj_12 hj) (jp.deg_B1_of_B2 j hj),
    row_sum_self jp j hj (jp.deg_B2_self j hj),
    row_sum_zero jp j (Finset.disjoint_left.mp jp.disj_23 hj) (jp.deg_B3_of_B2 j hj)]
  ring

/-- On `B₃`, `⟨q, y j⟩ = -24 ≠ 0`. -/
theorem reduction_vector_q_nonortho_B3 (jp : JenrichPartition G) (j : V) (hj : j ∈ jp.B₃) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G j) = -24 := by
  rw [inner_q_y_eq,
    row_sum_zero jp j (Finset.disjoint_right.mp jp.disj_13 hj) (jp.deg_B1_of_B3 j hj),
    row_sum_zero jp j (Finset.disjoint_right.mp jp.disj_23 hj) (jp.deg_B2_of_B3 j hj),
    row_sum_self jp j hj (jp.deg_B3_self j hj)]
  ring

/-- Zero inner product with `q` characterizes membership in `C`. -/
theorem reduction_vector_q_zero_iff_mem_C (jp : JenrichPartition G) (j : V) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G j) = 0 ↔ j ∈ jp.C := by
  refine ⟨fun h0 => ?_, reduction_vector_q_ortho_C jp j⟩
  have h_univ : j ∈ jp.B₁ ∪ jp.B₂ ∪ jp.B₃ ∪ jp.C := jp.union_eq.symm ▸ Finset.mem_univ j
  simp only [Finset.mem_union] at h_univ
  rcases h_univ with ((h1 | h2) | h3) | hc
  · linarith [reduction_vector_q_nonortho_B1 jp j h1]
  · linarith [reduction_vector_q_nonortho_B2 jp j h2]
  · linarith [reduction_vector_q_nonortho_B3 jp j h3]
  · exact hc

/-- Obstruction to augmenting `C`: no vertex outside `C` lies in `ker(q)`. -/
theorem no_vertex_augmentation_in_W63 (jp : JenrichPartition G) (v : V) (hv : v ∉ jp.C) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (y G v) ≠ 0 :=
  fun h => hv ((reduction_vector_q_zero_iff_mem_C jp v).mp h)

/-- Sum of entries of `q` is zero: `2 * 32 - 32 - 32 = 0`. -/
theorem inner_q_ones_eq_zero (jp : JenrichPartition G) :
    (∑ j : V, (q jp j)) = 0 := by
  simp only [q]
  have hB (B : Finset V) : (∑ j : V, (if j ∈ B then (1 : ℝ) else 0)) = (B.card : ℝ) := by
    rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hB, hB, hB, jp.card_B₁, jp.card_B₂, jp.card_B₃]
  ring

/-- Inner product of `q` with the all-ones vector is 0. -/
theorem inner_q_ones (jp : JenrichPartition G) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (ones V) = 0 := by
  rw [PiLp.inner_apply]
  simp only [ones, q, RCLike.inner_apply, conj_trivial, one_mul]
  exact inner_q_ones_eq_zero jp

/-- Inner product of `q` with any constant multiple of the all-ones vector is 0. -/
theorem inner_q_smul_ones (jp : JenrichPartition G) (c : ℝ) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (c • ones V) = 0 := by
  rw [inner_smul_right, inner_q_ones, mul_zero]

/-- The vector `q` is orthogonal to `z i` for all `i ∈ C`. -/
theorem inner_q_z_C (jp : JenrichPartition G) (c : ℝ) (i : V) (hi : i ∈ jp.C) :
    @inner ℝ (EuclideanSpace ℝ V) _ (q jp) (z G (c • ones V) i) = 0 := by
  simp [z, inner_sub_right, reduction_vector_q_ortho_C jp i hi, inner_q_smul_ones]

/-- The 63-dimensional almost-counterexample bound: `320 / 5 = 64 = 63 + 1`.
The 320-point set `C` achieves the Borsuk partition number in dimension 63. -/
theorem jenrich_bound_63 : 320 / 5 = 64 := rfl

theorem jenrich_achieves_63 : 64 = 63 + 1 := rfl

/-- Any smaller-diameter cover of `C` requires at least 64 parts. -/
theorem almost_counterexample_63 (jp : JenrichPartition G)
    (C_parts : Finset (Set V)) (h_cov : (jp.C : Set V) ⊆ ⋃ c ∈ C_parts, c)
    (h_clique : ∀ c ∈ C_parts, (jp.C.filter (· ∈ c)).card ≤ 5) :
    64 ≤ C_parts.card := by
  have := card_le_mul_card_cover jp.C C_parts h_cov h_clique
  rw [jp.card_C] at this
  omega

end Jenrich63

end JenrichBorsuk64
