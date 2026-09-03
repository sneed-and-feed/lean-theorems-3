import Formalization.AlonBoppana.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix Finset
open Classical

variable {V : Type*} [Fintype V]

namespace AlonBoppana

/-! ### Part 2: Spherical Shells and Metric Graph Geometry -/

/-- Spherical shell $S_k(x_0)$ of vertices at graph distance exactly $k$ from $x_0$. -/
noncomputable def sphericalShell (G : SimpleGraph V) (x_0 : V) (k : ℕ) : Finset V :=
  Finset.filter (fun v => G.dist x_0 v = k) Finset.univ

/-- Membership in a spherical shell corresponds to graph distance. -/
theorem sphericalShell_mem_iff (G : SimpleGraph V) (x_0 : V) (k : ℕ) (v : V) :
    v ∈ sphericalShell G x_0 k ↔ G.dist x_0 v = k := by
  simp [sphericalShell]

/-- Spherical shells at distinct distances are disjoint. -/
theorem sphericalShell_disjoint (G : SimpleGraph V) (x_0 : V) {j k : ℕ} (h : j ≠ k) :
    Disjoint (sphericalShell G x_0 j) (sphericalShell G x_0 k) := by
  rw [Finset.disjoint_left]
  intro x hj hk
  rw [sphericalShell_mem_iff] at hj hk
  exact h (hj.symm.trans hk)

/-- The 0-th spherical shell contains only the base point $x_0$ (for connected graphs). -/
theorem sphericalShell_zero (G : SimpleGraph V) (hconn : G.Connected) (x_0 : V) :
    sphericalShell G x_0 0 = {x_0} := by
  ext v
  simp [sphericalShell_mem_iff, hconn.dist_eq_zero_iff, eq_comm]

/-- The 1-st spherical shell equals the neighbor finset of $x_0$. -/
theorem sphericalShell_one (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) :
    sphericalShell G x_0 1 = G.neighborFinset x_0 := by
  ext v
  simp [sphericalShell_mem_iff, SimpleGraph.mem_neighborFinset, SimpleGraph.dist_eq_one_iff_adj]

/-- Adjacency in a graph restricts distances to shell neighbors by at most 1. -/
theorem sphericalShell_adj_cases (G : SimpleGraph V) (x_0 : V) {j k : ℕ} {u v : V}
    (hu : u ∈ sphericalShell G x_0 j) (hv : v ∈ sphericalShell G x_0 k) (hadj : G.Adj u v) :
    k = j ∨ k = j + 1 ∨ k = j - 1 := by
  rw [sphericalShell_mem_iff] at hu hv
  have h := hadj.diff_dist_adj (u := x_0)
  rw [hu, hv] at h
  exact h

/-- No edges exist between spherical shells differing in distance by 2 or more. -/
theorem not_adj_of_dist_ge_two (G : SimpleGraph V) (x_0 : V) {j k : ℕ} {u v : V}
    (hu : u ∈ sphericalShell G x_0 j) (hv : v ∈ sphericalShell G x_0 k) (hdiff : j + 2 ≤ k) :
    ¬ G.Adj u v := fun hadj => by
  have h := sphericalShell_adj_cases G x_0 hu hv hadj
  rcases h with rfl | rfl | rfl <;> omega

/-! ### Part 3: Shell Neighborhood Distribution and Degree Splitting -/

/-- Backward neighbors of $v \in S_k(x_0)$ in $S_{k-1}(x_0)$. -/
noncomputable def backwardNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) : Finset V :=
  G.neighborFinset v ∩ sphericalShell G x_0 (k - 1)

/-- Internal neighbors of $v \in S_k(x_0)$ in $S_k(x_0)$. -/
noncomputable def internalNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) : Finset V :=
  G.neighborFinset v ∩ sphericalShell G x_0 k

/-- Forward neighbors of $v \in S_k(x_0)$ in $S_{k+1}(x_0)$. -/
noncomputable def forwardNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) : Finset V :=
  G.neighborFinset v ∩ sphericalShell G x_0 (k + 1)

/-- In a connected graph, every vertex at distance $k \ge 1$ has a neighbor at distance $k - 1$. -/
theorem exists_neighbor_dist_sub_one (G : SimpleGraph V) (x_0 : V) (hconn : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : G.dist x_0 v = k) :
    ∃ w : V, G.Adj v w ∧ G.dist x_0 w = k - 1 := by
  rcases SimpleGraph.Connected.exists_walk_length_eq_dist hconn v x_0 with ⟨p, hp⟩
  have hv' : G.dist v x_0 = k := by rw [SimpleGraph.dist_comm, hv]
  rw [hv'] at hp
  cases p with
  | nil =>
    have : 0 = k := by simpa using hp
    omega
  | cons hadj p' =>
    rename_i w
    have hp' : p'.length = k - 1 := by
      have : p'.length + 1 = k := by simpa [SimpleGraph.Walk.length_cons] using hp
      omega
    have hdist_le : G.dist w x_0 ≤ k - 1 := by
      rw [← hp']; exact G.dist_le p'
    rw [SimpleGraph.dist_comm (u := w) (v := x_0)] at hdist_le
    have h_tri := hadj.diff_dist_adj (u := x_0)
    rw [hv] at h_tri
    have hdist_eq : G.dist x_0 w = k - 1 := by omega
    exact ⟨w, hadj, hdist_eq⟩

/-- Every vertex in $S_k(x_0)$ ($k \ge 1$) has at least 1 backward neighbor in $S_{k-1}(x_0)$. -/
theorem card_backwardNeighbors_ge_one (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    (hconn : G.Connected) {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    1 ≤ (backwardNeighbors G x_0 k v).card := by
  rw [sphericalShell_mem_iff] at hv
  rcases exists_neighbor_dist_sub_one G x_0 hconn hk hv with ⟨w, hadj, hw⟩
  have hw_mem : w ∈ backwardNeighbors G x_0 k v := by
    simp only [backwardNeighbors, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      sphericalShell_mem_iff]
    exact ⟨hadj, hw⟩
  exact Finset.card_pos.mpr ⟨w, hw_mem⟩

/-- All neighbors of $v \in S_k(x_0)$ lie in $S_{k-1} \cup S_k \cup S_{k+1}$. -/
theorem neighbor_subset_shells (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    G.neighborFinset v ⊆ backwardNeighbors G x_0 k v ∪ internalNeighbors G x_0 k v ∪ forwardNeighbors G x_0 k v := by
  intro w hw
  rw [sphericalShell_mem_iff] at hv
  have hadj : G.Adj v w := by simpa [SimpleGraph.mem_neighborFinset] using hw
  have h_tri := hadj.diff_dist_adj (u := x_0)
  rw [hv] at h_tri
  simp only [Finset.mem_union, backwardNeighbors, internalNeighbors, forwardNeighbors,
    Finset.mem_inter, hw, true_and, sphericalShell_mem_iff]
  rcases h_tri with h1 | h2 | h3
  · left; right; exact h1
  · right; exact h2
  · left; left; exact h3

/-- The neighborhood of $v \in S_k(x_0)$ partitions into backward, internal, and forward neighbors. -/
theorem neighborFinset_eq_union (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    G.neighborFinset v = backwardNeighbors G x_0 k v ∪ internalNeighbors G x_0 k v ∪ forwardNeighbors G x_0 k v := by
  apply Finset.Subset.antisymm (neighbor_subset_shells G x_0 hv)
  intro w hw
  simp only [Finset.mem_union, backwardNeighbors, internalNeighbors, forwardNeighbors, Finset.mem_inter] at hw
  rcases hw with (⟨hw1, _⟩ | ⟨hw1, _⟩) | ⟨hw1, _⟩ <;> exact hw1

/-- Backward neighbors and internal neighbors are disjoint for $k \ge 1$. -/
theorem disjoint_backward_internal (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} (hk : 1 ≤ k) (v : V) :
    Disjoint (backwardNeighbors G x_0 k v) (internalNeighbors G x_0 k v) := by
  apply Finset.disjoint_of_subset_right Finset.inter_subset_right
  apply Finset.disjoint_of_subset_left Finset.inter_subset_right
  apply sphericalShell_disjoint; omega

/-- Backward neighbors and forward neighbors are disjoint. -/
theorem disjoint_backward_forward (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) :
    Disjoint (backwardNeighbors G x_0 k v) (forwardNeighbors G x_0 k v) := by
  apply Finset.disjoint_of_subset_right Finset.inter_subset_right
  apply Finset.disjoint_of_subset_left Finset.inter_subset_right
  apply sphericalShell_disjoint; omega

/-- Internal neighbors and forward neighbors are disjoint. -/
theorem disjoint_internal_forward (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V) (k : ℕ) (v : V) :
    Disjoint (internalNeighbors G x_0 k v) (forwardNeighbors G x_0 k v) := by
  apply Finset.disjoint_of_subset_right Finset.inter_subset_right
  apply Finset.disjoint_of_subset_left Finset.inter_subset_right
  apply sphericalShell_disjoint; omega

/-- Cardinality degree split across backward, internal, and forward neighbor sets. -/
theorem card_neighbors_split (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    (G.neighborFinset v).card =
      (backwardNeighbors G x_0 k v).card + (internalNeighbors G x_0 k v).card + (forwardNeighbors G x_0 k v).card := by
  rw [neighborFinset_eq_union G x_0 hv, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint (disjoint_backward_internal G x_0 hk v)]
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_backward_forward G x_0 k v, disjoint_internal_forward G x_0 k v⟩

/-- In a $d$-regular connected graph, any vertex at distance $k \ge 1$ has at most $d - 1$ forward neighbors. -/
theorem forwardNeighbors_card_le_d_sub_one (G : SimpleGraph V) [DecidableRel G.Adj] (x_0 : V)
    {d : ℕ} (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    {k : ℕ} (hk : 1 ≤ k) {v : V} (hv : v ∈ sphericalShell G x_0 k) :
    (forwardNeighbors G x_0 k v).card ≤ d - 1 := by
  have h_split := card_neighbors_split G x_0 hk hv
  have h_deg : (G.neighborFinset v).card = d := by
    rw [← SimpleGraph.degree, hreg v]
  rw [h_deg] at h_split
  have h_back := card_backwardNeighbors_ge_one G x_0 hconn hk hv
  omega

end AlonBoppana
