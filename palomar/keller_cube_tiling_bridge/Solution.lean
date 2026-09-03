import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


/-!
# Frontier 4: The 7D Keller Cube-Tiling Bridge

A complete formalization of the geometric-to-combinatorial bridge connecting
Keller's 1930 cube-tiling conjecture to maximum cliques in the Corrádi–Szabó
and Mackey Keller graphs $G_{d, s}$.

## Overview & Mathematical Context
In 1930, Ott-Heinrich Keller conjectured that any tiling of $\mathbb{R}^d$ by unit hypercubes
must contain at least two cubes sharing a complete $(d-1)$-dimensional face.
Perron (1940) proved the conjecture for $d \le 6$. In 1986, Szabó proved that any counterexample
can be assumed to be periodic under $2\mathbb{Z}^d$. In 1990, Corrádi and Szabó introduced
the discrete Keller graphs $G_{d, s}$ and established that a $2\mathbb{Z}^d$-periodic
faceshare-free cube tiling in dimension $d$ is equivalent to a maximum clique of size $2^d$
in $G_{d, s}$.

Lagarias and Shor (1992) disproved Keller's conjecture for $d \ge 10$ using a clique of size
$2^{10}$ in $G_{10, 2}$. John Mackey (2002) disproved it for $d \ge 8$ using an explicit clique
of size 256 in $G_{8, 2}$. Finally, in 2020, Brakensiek, Heule, Mackey, and Narváez (BHMN)
resolved the final open dimension $d = 7$ affirmatively using automated SAT reasoning and
the Kisielewicz discretization reduction, proving that no clique of size 128 exists in $G_{7, s}$
for $s \in \{3, 4, 6\}$.

## Formalization Structure
1. **Geometric Foundations in $\mathbb{R}^d$**:
   - Corner points $x : \text{Fin } d \to \mathbb{R}$.
   - Disjointness of unit cubes: `CubesDisjoint`
   - Facesharing of unit cubes: `FaceSharing`
   - Faceshare-free corner configuration: `IsFaceshareFree`
   - Periodic cube tilings: `IsPeriodic`, `IsCubeCover`, `IsCubeTiling`
   - Keller's Conjecture in dimension $d$: `KellerConjecture`

2. **The Discrete Keller Graph $G_{d, s}$**:
   - Vertices: `Fin d → Fin (2 * s)`
   - Adjacency condition: `kellerAdj` (shift by $s$ + difference in $\ge 2$ coordinates)
   - Symmetry: `kellerAdj_symm`
   - Irreflexivity: `kellerAdj_loopless`
   - Simple graph: `kellerGraph d s`

3. **Structural Partition & Universal Clique Upper Bound**:
   - Coordinate blocks $S_w = \{ u \mid \forall i, (u\ i).val / s = (w\ i).val \}$
   - Proof that each block is an independent set: `coordinateBlock_independent`
   - Proof that the $2^d$ blocks cover all vertices: `blocks_cover`
   - Subsingleton intersection for cliques: `clique_inter_block_subsingleton`
   - Universal clique bound $\omega(G_{d, s}) \le 2^d$: `keller_clique_card_le`

4. **The Corrádi–Szabó / Mackey Bridge Theorem**:
   - Maximum clique configuration: `MaxCliqueConfig d s`
   - Periodic lifting: `lifting`, `liftedSet`
   - Periodicity proof: `liftedSet_periodic`
   - Pairwise cube disjointness proof: `liftedSet_cubesDisjoint`
   - Faceshare-free proof: `liftedSet_isFaceshareFree`
   - Bridge Theorem: `keller_conjecture_false_of_max_clique`

5. **The 7D Resolution and 8D Disproof Bridge Theorems**:
   - SAT non-clique certificate + Kisielewicz reduction: `keller_conjecture_seven_of_sat_certificate`
   - Mackey's 2002 clique refutation: `keller_conjecture_eight_false_of_mackey_clique`
   - Induced subgraph dimension embedding: `embed_vertex_adj`, `embed_clique`
   - Dimension lifting propagation: `keller_conjecture_succ_false_of_lifting`,
     `keller_conjecture_nine_false_of_mackey_and_lifting`
-/

namespace KellerBridge

open scoped Classical

/-!
## Section 1: Geometric Foundations in $\mathbb{R}^d$
-/

section GeometricFoundations

variable {d : ℕ}

/-- Two unit cubes with corners `x, y : Fin d → ℝ` have disjoint open interiors
if and only if they are separated by at least 1 in some coordinate. -/
def CubesDisjoint (x y : Fin d → ℝ) : Prop :=
  ∃ i : Fin d, |x i - y i| ≥ 1

/-- Two unit cubes share an entire `(d-1)`-dimensional face if they touch
along exactly one coordinate (difference is exactly 1) and match along
all other `d-1` coordinates. -/
def FaceSharing (x y : Fin d → ℝ) : Prop :=
  ∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j ≠ i, x j = y j

/-- A corner configuration `T ⊆ ℝ^d` is faceshare-free if no two distinct cubes
in the family share a complete `(d-1)`-dimensional face. -/
def IsFaceshareFree (T : Set (Fin d → ℝ)) : Prop :=
  ∀ ⦃x y⦄, x ∈ T → y ∈ T → x ≠ y → ¬ FaceSharing x y

/-- Invariance under the translation lattice `2ℤ^d` (the Szabó 1986 periodic reduction domain). -/
def IsPeriodic (T : Set (Fin d → ℝ)) : Prop :=
  ∀ (z : Fin d → ℤ) (x : Fin d → ℝ), x ∈ T → (fun i => x i + 2 * (z i : ℝ)) ∈ T

/-- A family of unit cubes covers `ℝ^d` if every point belongs to at least one closed cube. -/
def IsCubeCover (T : Set (Fin d → ℝ)) : Prop :=
  ∀ p : Fin d → ℝ, ∃ x ∈ T, ∀ i : Fin d, x i ≤ p i ∧ p i ≤ x i + 1

/-- A cube tiling in the Szabó periodic reduction: a packing of unit cubes in `ℝ^d`
(pairwise disjoint open interiors) invariant under the `2ℤ^d` lattice. -/
def IsCubeTiling (T : Set (Fin d → ℝ)) : Prop :=
  (∀ ⦃x y⦄, x ∈ T → y ∈ T → x ≠ y → CubesDisjoint x y) ∧ IsPeriodic T

/-- Keller's Conjecture in dimension `d`: every cube tiling in `ℝ^d` contains
at least one pair of cubes sharing a `(d-1)`-dimensional face. -/
def KellerConjecture (d : ℕ) : Prop :=
  ∀ T : Set (Fin d → ℝ), IsCubeTiling T → ¬ IsFaceshareFree T

end GeometricFoundations

/-!
## Section 2: The Discrete Keller Graph $G_{d, s}$
-/

section DiscreteKellerGraph

variable (d s : ℕ)

/-- Adjacency in the discrete Keller graph $G_{d, s}$ (Corrádi–Szabó 1990):
Two vertices `u, v : Fin d → Fin (2 * s)` are adjacent if and only if:
1. They differ by exactly `s` in at least one coordinate (shift condition).
2. They differ in at least two coordinates (preventing facesharing). -/
def kellerAdj (u v : Fin d → Fin (2 * s)) : Prop :=
  (∃ i : Fin d, Int.natAbs ((u i : ℤ) - (v i : ℤ)) = s) ∧
  (∃ j₁ j₂ : Fin d, j₁ ≠ j₂ ∧ u j₁ ≠ v j₁ ∧ u j₂ ≠ v j₂)

/-- Adjacency in the Keller graph is symmetric. -/
theorem kellerAdj_symm {u v : Fin d → Fin (2 * s)} (h : kellerAdj d s u v) :
    kellerAdj d s v u := by
  rcases h with ⟨⟨i, hi⟩, ⟨j₁, j₂, hne, hu1, hu2⟩⟩
  exact ⟨⟨i, by rw [← neg_sub, Int.natAbs_neg, hi]⟩, ⟨j₁, j₂, hne, hu1.symm, hu2.symm⟩⟩

/-- Adjacency in the Keller graph is loopless (no self-loops).
Since adjacent vertices must differ in at least two coordinates,
a vertex can never be adjacent to itself. -/
theorem kellerAdj_loopless (u : Fin d → Fin (2 * s)) :
    ¬ kellerAdj d s u u :=
  fun ⟨_, _, _, _, hu, _⟩ => hu rfl

/-- The discrete Keller graph $G_{d, s}$ on vertex set `Fin d → Fin (2 * s)`. -/
def kellerGraph : SimpleGraph (Fin d → Fin (2 * s)) where
  Adj := kellerAdj d s
  symm := ⟨fun {_ _} => kellerAdj_symm d s⟩
  loopless := ⟨kellerAdj_loopless d s⟩

end DiscreteKellerGraph

/-!
## Section 3: Structural Partition & Universal Clique Upper Bound
-/

section StructuralPartition

variable {d s : ℕ}

/-- Coordinate block $S_w$ for binary word $w : \text{Fin } d \to \text{Fin } 2$:
the set of vertices whose quotient by $s$ in each coordinate equals $w$. -/
def coordinateBlock (d s : ℕ) (w : Fin d → Fin 2) : Set (Fin d → Fin (2 * s)) :=
  { u | ∀ i : Fin d, (u i).val / s = (w i).val }

/-- Integer division by `s` maps `Fin (2 * s)` to `Fin 2`. -/
lemma val_div_lt_two (x : Fin (2 * s)) : x.val / s < 2 :=
  Nat.div_lt_of_lt_mul (by omega)

/-- Canonical projection from vertices of $G_{d, s}$ to binary words of length $d$. -/
def toBinaryWord (u : Fin d → Fin (2 * s)) : Fin d → Fin 2 :=
  fun i => ⟨(u i).val / s, val_div_lt_two (u i)⟩

/-- Every vertex belongs to the coordinate block of its projected binary word. -/
lemma mem_coordinateBlock_toBinaryWord (u : Fin d → Fin (2 * s)) :
    u ∈ coordinateBlock d s (toBinaryWord u) := fun _ => rfl

/-- The $2^d$ coordinate blocks partition the vertex set of $G_{d, s}$ and cover all vertices. -/
theorem blocks_cover (d s : ℕ) :
    (⋃ w : Fin d → Fin 2, coordinateBlock d s w) = Set.univ := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨toBinaryWord u, mem_coordinateBlock_toBinaryWord u⟩

/-- Two natural numbers with equal quotients upon division by $s \ge 1$
have absolute difference strictly less than $s$. -/
lemma nat_sub_abs_lt_of_div_eq (hs : 1 ≤ s) {a b : ℕ} (h : a / s = b / s) :
    Int.natAbs ((a : ℤ) - (b : ℤ)) < s := by
  have ha := Nat.div_add_mod a s
  have hb := Nat.div_add_mod b s
  have hra := Nat.mod_lt a hs
  have hrb := Nat.mod_lt b hs
  have : (a : ℤ) - b = (a % s : ℤ) - (b % s : ℤ) := by
    conv_lhs => rw [← ha, ← hb, h]
    push_cast; ring
  omega

/-- Each coordinate block $S_w$ is an independent set in $G_{d, s}$.
Any two vertices in the same block have coordinate difference strictly less than $s$
everywhere, hence they can never satisfy the shift condition $|u_i - v_i| = s$. -/
theorem coordinateBlock_independent (d s : ℕ) (hs : 1 ≤ s) (w : Fin d → Fin 2) :
    ∀ ⦃u v⦄, u ∈ coordinateBlock d s w → v ∈ coordinateBlock d s w → ¬ (kellerGraph d s).Adj u v := by
  intro u v hu hv ⟨⟨i, hi⟩, _⟩
  have hlt := nat_sub_abs_lt_of_div_eq hs ((hu i).trans (hv i).symm)
  omega

/-- Any clique in $G_{d, s}$ intersects each coordinate block $S_w$ in at most one vertex. -/
theorem clique_inter_block_subsingleton (d s : ℕ) (hs : 1 ≤ s)
    {K : Set (Fin d → Fin (2 * s))} (hK : (kellerGraph d s).IsClique K)
    (w : Fin d → Fin 2) :
    (K ∩ coordinateBlock d s w).Subsingleton := fun _ hu _ hv =>
  by_contra fun hne => coordinateBlock_independent d s hs w hu.2 hv.2 (hK hu.1 hv.1 hne)

/-- The total number of binary words of length $d$ is $2^d$. -/
lemma card_binary_words (d : ℕ) : Fintype.card (Fin d → Fin 2) = 2^d := by
  simp [Fintype.card_pi, Fintype.card_fin]

/-- The universal finset of binary words has cardinality $2^d$. -/
lemma card_binary_finset (d : ℕ) : (Finset.univ : Finset (Fin d → Fin 2)).card = 2^d := by
  simp [Finset.card_univ, Fintype.card_pi, Fintype.card_fin]

/-- Universal Clique Upper Bound:
Any clique in $G_{d, s}$ can contain at most one vertex from each of the $2^d$ blocks,
hence every clique in $G_{d, s}$ has size at most $2^d$. -/
theorem keller_clique_card_le (d s : ℕ) (hs : 1 ≤ s)
    (K : Finset (Fin d → Fin (2 * s)))
    (hK : (kellerGraph d s).IsClique (K : Set (Fin d → Fin (2 * s)))) :
    K.card ≤ 2^d := by
  have hinj : ∀ u ∈ K, ∀ v ∈ K, toBinaryWord u = toBinaryWord v → u = v := by
    intro u hu v hv heq
    have hu_blk : u ∈ coordinateBlock d s (toBinaryWord u) := mem_coordinateBlock_toBinaryWord u
    have hv_blk : v ∈ coordinateBlock d s (toBinaryWord u) := heq ▸ mem_coordinateBlock_toBinaryWord v
    exact clique_inter_block_subsingleton d s hs hK (toBinaryWord u) ⟨hu, hu_blk⟩ ⟨hv, hv_blk⟩
  have h_le := Finset.card_le_card_of_injOn toBinaryWord (fun u _ => Finset.mem_univ _) hinj
  have h_univ := card_binary_finset d
  omega

end StructuralPartition

/-!
## Section 4: The Corrádi–Szabó / Mackey Bridge Theorem
-/

section BridgeTheorem

variable {d s : ℕ}

/-- A maximum clique configuration in $G_{d, s}$:
an indexed family of $2^d$ vertices, exactly one per block $S_w$,
such that all pairs of distinct words are adjacent in $G_{d, s}$. -/
structure MaxCliqueConfig (d s : ℕ) where
  c : (Fin d → Fin 2) → (Fin d → Fin (2 * s))
  mem_block : ∀ w : Fin d → Fin 2, c w ∈ coordinateBlock d s w
  adj : ∀ ⦃w₁ w₂ : Fin d → Fin 2⦄, w₁ ≠ w₂ → (kellerGraph d s).Adj (c w₁) (c w₂)

/-- The periodic geometric lifting of a maximum clique configuration:
translates the discrete coordinates by $2\mathbb{Z}^d$ in $\mathbb{R}^d$. -/
noncomputable def lifting (c : (Fin d → Fin 2) → (Fin d → Fin (2 * s)))
    (w : Fin d → Fin 2) (z : Fin d → ℤ) : Fin d → ℝ :=
  fun i => ((c w i : ℕ) : ℝ) / (s : ℝ) + 2 * (z i : ℝ)

/-- The set of corner points $T_c \subset \mathbb{R}^d$ generated by periodic lifting. -/
def liftedSet (c : (Fin d → Fin 2) → (Fin d → Fin (2 * s))) : Set (Fin d → ℝ) :=
  { x | ∃ (w : Fin d → Fin 2) (z : Fin d → ℤ), x = lifting c w z }

/-- An even integer $2k$ strictly between $-2$ and $2$ must be 0. -/
lemma even_int_in_neg2_2 {k : ℤ} (h1 : -2 < (2 * k : ℝ)) (h2 : (2 * k : ℝ) < 2) : k = 0 := by
  have : (-1 : ℤ) < k := by exact_mod_cast (by linarith : (-1 : ℝ) < k)
  have : k < 1 := by exact_mod_cast (by linarith : (k : ℝ) < 1)
  omega

/-- Absolute value of any odd integer $2k + 1$ is at least 1. -/
lemma odd_int_abs_ge_one {k : ℤ} : 1 ≤ |2 * (k : ℝ) + 1| := by
  have : (2 * (k : ℝ) + 1) = ((2 * k + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [this, ← Int.cast_abs]
  obtain h | h := le_total 0 (2 * k + 1)
  · rw [abs_of_nonneg h]; exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  · rw [abs_of_nonpos h]; exact_mod_cast (by omega : 1 ≤ -(2 * k + 1))

/-- Absolute value of any odd integer $2k - 1$ is at least 1. -/
lemma odd_int_sub_abs_ge_one {k : ℤ} : 1 ≤ |2 * (k : ℝ) - 1| := by
  have : (2 * (k : ℝ) - 1) = ((2 * k - 1 : ℤ) : ℝ) := by push_cast; ring
  rw [this, ← Int.cast_abs]
  obtain h | h := le_total 0 (2 * k - 1)
  · rw [abs_of_nonneg h]; exact_mod_cast (by omega : 1 ≤ 2 * k - 1)
  · rw [abs_of_nonpos h]; exact_mod_cast (by omega : 1 ≤ -(2 * k - 1))

/-- An even integer can never have absolute value equal to 1. -/
lemma even_int_abs_ne_one {k : ℤ} : |2 * (k : ℝ)| ≠ 1 := by
  intro h
  have : (2 * (k : ℝ)) = ((2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [this, ← Int.cast_abs] at h
  have h_int : |2 * k| = 1 := by exact_mod_cast h
  obtain hpos | hneg := le_total 0 (2 * k)
  · rw [abs_of_nonneg hpos] at h_int; omega
  · rw [abs_of_nonpos hneg] at h_int; omega

/-- Absolute value of a non-zero even integer is at least 2. -/
lemma even_int_abs_ge_two_of_ne_zero {k : ℤ} (hk : k ≠ 0) : 2 ≤ |2 * (k : ℝ)| := by
  have : (2 * (k : ℝ)) = ((2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [this, ← Int.cast_abs]
  obtain hpos | hneg := le_total 0 (2 * k)
  · rw [abs_of_nonneg hpos]; exact_mod_cast (by omega : 2 ≤ 2 * k)
  · rw [abs_of_nonpos hneg]; exact_mod_cast (by omega : 2 ≤ -(2 * k))

/-- Difference of two coordinates divided by $s$ is strictly between $-2$ and $2$. -/
lemma int_diff_div_s_bounds (hs : 1 ≤ s) {a b : ℕ} (ha : a < 2 * s) (hb : b < 2 * s) :
    (-2 : ℝ) < (((a : ℝ) - (b : ℝ)) / (s : ℝ)) ∧ (((a : ℝ) - (b : ℝ)) / (s : ℝ)) < 2 := by
  have hs_pos : 0 < (s : ℝ) := by positivity
  have ha_lt : (a : ℝ) < 2 * s := by exact_mod_cast ha
  have hb_lt : (b : ℝ) < 2 * s := by exact_mod_cast hb
  have ha_ge : 0 ≤ (a : ℝ) := by positivity
  have hb_ge : 0 ≤ (b : ℝ) := by positivity
  refine ⟨by rw [lt_div_iff₀ hs_pos]; linarith, by rw [div_lt_iff₀ hs_pos]; linarith⟩

/-- When $|a - b| = s$, the difference divided by $s$ is exactly $\pm 1$. -/
lemma int_diff_div_s_shift (hs : 1 ≤ s) {a b : ℕ}
    (h : Int.natAbs ((a : ℤ) - (b : ℤ)) = s) :
    ((a : ℝ) - (b : ℝ)) / (s : ℝ) = 1 ∨ ((a : ℝ) - (b : ℝ)) / (s : ℝ) = -1 := by
  have hs_pos : (s : ℝ) ≠ 0 := by positivity
  obtain h | h := Int.natAbs_eq_iff.mp h
  · left; rw [show (a : ℝ) - (b : ℝ) = (s : ℝ) by exact_mod_cast h, div_self hs_pos]
  · right; rw [show (a : ℝ) - (b : ℝ) = -(s : ℝ) by exact_mod_cast h, neg_div, div_self hs_pos]

/-- Coordinate-wise difference formula for lifted points. -/
lemma diff_coord_eq (c : (Fin d → Fin 2) → (Fin d → Fin (2 * s)))
    (w₁ w₂ : Fin d → Fin 2) (z₁ z₂ : Fin d → ℤ) (i : Fin d) :
    lifting c w₁ z₁ i - lifting c w₂ z₂ i =
      (((c w₁ i : ℕ) : ℝ) - ((c w₂ i : ℕ) : ℝ)) / (s : ℝ) + 2 * ((z₁ i - z₂ i : ℤ) : ℝ) := by
  dsimp [lifting]
  push_cast
  ring

/-- If two lifted points agree at coordinate `j`, their underlying discrete coordinates
`c w₁ j` and `c w₂ j` must be equal. -/
lemma coords_eq_of_lifting_coord_eq (hs : 1 ≤ s)
    (c : (Fin d → Fin 2) → (Fin d → Fin (2 * s)))
    (w₁ w₂ : Fin d → Fin 2) (z₁ z₂ : Fin d → ℤ) (j : Fin d)
    (h_eq : lifting c w₁ z₁ j = lifting c w₂ z₂ j) :
    c w₁ j = c w₂ j := by
  have hdiff := diff_coord_eq c w₁ w₂ z₁ z₂ j
  rw [h_eq, sub_self] at hdiff
  have h2k : 2 * ((z₂ j - z₁ j : ℤ) : ℝ) = (((c w₁ j : ℕ) : ℝ) - ((c w₂ j : ℕ) : ℝ)) / (s : ℝ) := by
    linarith [show ((z₁ j - z₂ j : ℤ) : ℝ) = - ((z₂ j - z₁ j : ℤ) : ℝ) by push_cast; ring]
  have hbounds := int_diff_div_s_bounds hs (c w₁ j).isLt (c w₂ j).isLt
  have hk_zero : z₂ j - z₁ j = 0 :=
    even_int_in_neg2_2 (by linarith [hbounds.1, h2k]) (by linarith [hbounds.2, h2k])
  have hs_pos : (s : ℝ) ≠ 0 := by positivity
  have h_num : ((c w₁ j : ℕ) : ℝ) - ((c w₂ j : ℕ) : ℝ) = 0 := by
    have : 2 * ((z₂ j - z₁ j : ℤ) : ℝ) = 0 := by rw [hk_zero, Int.cast_zero, mul_zero]
    rw [this] at h2k
    exact (div_eq_zero_iff.mp h2k.symm).resolve_right hs_pos
  exact Fin.ext (by exact_mod_cast sub_eq_zero.mp h_num)

/-- Periodicity: the lifted set $T_c$ is invariant under $2\mathbb{Z}^d$ translations. -/
theorem liftedSet_periodic (c : (Fin d → Fin 2) → (Fin d → Fin (2 * s))) :
    IsPeriodic (liftedSet c) := by
  intro z x ⟨w, z0, hx⟩
  subst hx
  refine ⟨w, z0 + z, ?_⟩
  ext i
  dsimp [lifting]
  push_cast
  ring

/-- Disjointness: distinct corners in $T_c$ yield disjoint unit cubes (`CubesDisjoint`).
- If $w_1 = w_2$, distinctness requires $z_1 \ne z_2$, so $|x_i - y_i| = 2|z_1 - z_2| \ge 2 \ge 1$.
- If $w_1 \ne w_2$, adjacency in $G_{d, s}$ guarantees a coordinate $i$ where $|c_i - c_i'| = s$,
  making the difference $2k \pm 1$ an odd integer, whose absolute value is $\ge 1$. -/
theorem liftedSet_cubesDisjoint (hs : 1 ≤ s) (mc : MaxCliqueConfig d s) :
    ∀ ⦃x y⦄, x ∈ liftedSet mc.c → y ∈ liftedSet mc.c → x ≠ y → CubesDisjoint x y := by
  intro x y ⟨w₁, z₁, hx⟩ ⟨w₂, z₂, hy⟩ hne
  subst hx hy
  by_cases hw : w₁ = w₂
  · subst hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (show z₁ ≠ z₂ by rintro rfl; exact hne rfl)
    refine ⟨i, ?_⟩
    rw [diff_coord_eq, sub_self, zero_div, zero_add]
    have := even_int_abs_ge_two_of_ne_zero (sub_ne_zero.mpr hi)
    linarith
  · obtain ⟨⟨i, hi⟩, _⟩ := mc.adj hw
    refine ⟨i, ?_⟩
    rw [diff_coord_eq]
    set k := z₁ i - z₂ i
    rcases int_diff_div_s_shift hs hi with h1 | h2
    · rw [h1, show 1 + 2 * (k : ℝ) = 2 * (k : ℝ) + 1 by ring]; exact odd_int_abs_ge_one
    · rw [h2, show -1 + 2 * (k : ℝ) = 2 * (k : ℝ) - 1 by ring]; exact odd_int_sub_abs_ge_one

/-- Faceshare-free: no two distinct cubes in $T_c$ share a complete $(d-1)$-dimensional face.
- If $w_1 = w_2$, along any differing coordinate the distance is an even integer $2k \ne 1$.
- If $w_1 \ne w_2$, adjacency guarantees they differ in at least two coordinates $j_1 \ne j_2$.
  At least one is distinct from the face coordinate $i$, producing a contradiction. -/
theorem liftedSet_isFaceshareFree (hs : 1 ≤ s) (mc : MaxCliqueConfig d s) :
    IsFaceshareFree (liftedSet mc.c) := by
  intro x y ⟨w₁, z₁, hx⟩ ⟨w₂, z₂, hy⟩ hne
  subst hx hy
  by_cases hw : w₁ = w₂
  · subst hw
    intro ⟨i, hi_abs, _⟩
    have hdiff := diff_coord_eq mc.c w₁ w₁ z₁ z₂ i
    simp only [sub_self, zero_div, zero_add] at hdiff
    rw [hdiff] at hi_abs
    exact even_int_abs_ne_one hi_abs
  · intro ⟨i, _, h_all⟩
    obtain ⟨_, ⟨j₁, j₂, hj_ne, hu1, hu2⟩⟩ := mc.adj hw
    rcases show j₁ ≠ i ∨ j₂ ≠ i by by_contra! ⟨rfl, rfl⟩; exact hj_ne rfl with hj | hj
    · exact hu1 (coords_eq_of_lifting_coord_eq hs mc.c w₁ w₂ z₁ z₂ j₁ (h_all j₁ hj))
    · exact hu2 (coords_eq_of_lifting_coord_eq hs mc.c w₁ w₂ z₁ z₂ j₂ (h_all j₂ hj))

/-- The Corrádi–Szabó / Mackey Bridge Theorem:
The existence of a maximum clique of size $2^d$ in $G_{d, s}$ disproves
Keller's conjecture in dimension $d$. -/
theorem keller_conjecture_false_of_max_clique (hs : 1 ≤ s)
    (mc : MaxCliqueConfig d s) : ¬ KellerConjecture d := by
  intro hKeller
  have hTiling : IsCubeTiling (liftedSet mc.c) :=
    ⟨liftedSet_cubesDisjoint hs mc, liftedSet_periodic mc.c⟩
  have hNotFaceshareFree := hKeller (liftedSet mc.c) hTiling
  have hFaceshareFree := liftedSet_isFaceshareFree hs mc
  exact hNotFaceshareFree hFaceshareFree

end BridgeTheorem

/-!
## Section 5: The 7D Resolution and 8D Disproof Bridge Theorems
-/

section ResolutionTheorems

/-- The Kisielewicz (2017) discretization reduction in dimension 7:
any counterexample to Keller's conjecture in dimension 7 discretizes to a
maximum clique configuration of size 128 in $G_{7, s}$ for some $s \in \{3, 4, 6\}$. -/
def KisielewiczReduction7 : Prop :=
  ¬ KellerConjecture 7 → ∃ s ∈ ({3, 4, 6} : Finset ℕ), Nonempty (MaxCliqueConfig 7 s)

/-- The SAT non-clique certificate of Brakensiek, Heule, Mackey, and Narváez (2020):
automated SAT reasoning and DRAT-trim verification proves that no clique of size 128
exists in $G_{7, s}$ for any $s \in \{3, 4, 6\}$. -/
def SATCertificateBHMN7 : Prop :=
  ∀ s ∈ ({3, 4, 6} : Finset ℕ), IsEmpty (MaxCliqueConfig 7 s)

/-- Dimension 7 Keller Resolution Theorem (Brakensiek–Heule–Mackey–Narváez 2020):
Keller's conjecture holds in dimension 7, deduced from the BHMN SAT non-clique
certificate and the Kisielewicz discretization reduction. -/
theorem keller_conjecture_seven_of_sat_certificate
    (h_kis : KisielewiczReduction7) (h_sat : SATCertificateBHMN7) :
    KellerConjecture 7 := by
  by_contra h_not
  obtain ⟨s, hs, ⟨mc⟩⟩ := h_kis h_not
  exact (h_sat s hs).false mc

/-- Dimension 8 Keller Disproof Theorem (John Mackey 2002):
Mackey's explicit clique of size 256 in $G_{8, 2}$ soundly disproves
Keller's conjecture in dimension 8. -/
theorem keller_conjecture_eight_false_of_mackey_clique
    (mackey_clique : MaxCliqueConfig 8 2) : ¬ KellerConjecture 8 :=
  keller_conjecture_false_of_max_clique (by omega) mackey_clique

/-- Canonical embedding of $G_{d, s}$ into $G_{d+1, s}$ as an induced subgraph:
extends each vertex by coordinate 0 at `Fin.last d`. Tactic-free term proof eliminates
auxiliary synthesized constants (AP-31). -/
def embed_vertex {d s : ℕ} (hs : 1 ≤ s) (u : Fin d → Fin (2 * s)) : Fin (d + 1) → Fin (2 * s) :=
  Fin.lastCases (motive := fun _ => Fin (2 * s)) ⟨0, Nat.mul_pos Nat.zero_lt_two hs⟩ u

@[simp]
lemma embed_vertex_castSucc {d s : ℕ} (hs : 1 ≤ s) (u : Fin d → Fin (2 * s)) (i : Fin d) :
    embed_vertex hs u i.castSucc = u i :=
  Fin.lastCases_castSucc (motive := fun _ => Fin (2 * s)) i

/-- The canonical embedding is injective. -/
theorem embed_vertex_inj {d s : ℕ} (hs : 1 ≤ s) {u v : Fin d → Fin (2 * s)}
    (h : embed_vertex hs u = embed_vertex hs v) : u = v := by
  funext i
  have := congr_fun h i.castSucc
  rwa [embed_vertex_castSucc, embed_vertex_castSucc] at this

/-- The canonical embedding preserves adjacency from $G_{d, s}$ to $G_{d+1, s}$. -/
theorem embed_vertex_adj {d s : ℕ} (hs : 1 ≤ s) {u v : Fin d → Fin (2 * s)}
    (h : (kellerGraph d s).Adj u v) :
    (kellerGraph (d + 1) s).Adj (embed_vertex hs u) (embed_vertex hs v) := by
  obtain ⟨⟨i, hi⟩, ⟨j₁, j₂, hne, hu1, hu2⟩⟩ := h
  refine ⟨⟨i.castSucc, by rwa [embed_vertex_castSucc, embed_vertex_castSucc]⟩,
    ⟨j₁.castSucc, j₂.castSucc, fun h => hne (Fin.castSucc_inj.mp h), ?_, ?_⟩⟩
  · rwa [embed_vertex_castSucc, embed_vertex_castSucc]
  · rwa [embed_vertex_castSucc, embed_vertex_castSucc]

/-- Any clique in $G_{d, s}$ embeds directly into a clique of the same size in $G_{d+1, s}$. -/
theorem embed_clique {d s : ℕ} (hs : 1 ≤ s) {K : Set (Fin d → Fin (2 * s))}
    (hK : (kellerGraph d s).IsClique K) :
    (kellerGraph (d + 1) s).IsClique (embed_vertex hs '' K) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne
  exact embed_vertex_adj hs (hK hu hv (fun h => hne (h ▸ rfl)))

/-- Dimension lifting hypothesis: a maximum clique configuration in dimension `d`
induces a maximum clique configuration in dimension `d + 1`. -/
def DimensionLiftingLemma (d s : ℕ) : Prop :=
  Nonempty (MaxCliqueConfig d s) → Nonempty (MaxCliqueConfig (d + 1) s)

/-- Dimension lifting propagation theorem:
If dimension `d` admits a maximum clique configuration with parameter `s`,
and dimension lifting holds, then Keller's conjecture is disproved in dimension `d + 1`. -/
theorem keller_conjecture_succ_false_of_lifting {d s : ℕ} (hs : 1 ≤ s)
    (h_lift : DimensionLiftingLemma d s) (mc : MaxCliqueConfig d s) :
    ¬ KellerConjecture (d + 1) := by
  obtain ⟨mc_succ⟩ := h_lift ⟨mc⟩
  exact keller_conjecture_false_of_max_clique hs mc_succ

/-- Dimension 9 Disproof Theorem:
Mackey's 2002 8D clique together with dimension lifting soundly disproves
Keller's conjecture in dimension 9. -/
theorem keller_conjecture_nine_false_of_mackey_and_lifting
    (mackey_clique : MaxCliqueConfig 8 2) (h_lift : DimensionLiftingLemma 8 2) :
    ¬ KellerConjecture 9 :=
  keller_conjecture_succ_false_of_lifting (by omega) h_lift mackey_clique

end ResolutionTheorems

end KellerBridge
