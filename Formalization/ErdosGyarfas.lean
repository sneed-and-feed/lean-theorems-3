/-
Copyright (c) 2026 Lean Theorems Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Theorems Contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# The Erdős–Gyárfás Conjecture and Girth Hunter Scaffold

The Erdős–Gyárfás conjecture (1975) asserts that every simple graph with minimum degree
$\delta(G) \ge 3$ contains a simple cycle of length $2^k$ for some $k \ge 2$
(i.e., of length 4, 8, 16, 32, ...).

This module formalizes:
1. `IsPowerOfTwoCycleLength`: predicate identifying cycle lengths that are powers of two $\ge 4$.
2. `HasPowerOfTwoCycle`: predicate for when a simple graph contains a power-of-two simple cycle.
3. `ErdosGyarfasConjecture`: the universal statement of the conjecture across finite graphs.
4. `CounterexampleCertificate`: a constructive, verifiable certificate witnessing a counterexample.
5. `disprove_erdos_gyarfas`: the sound meta-theorem deriving $\neg \text{ErdosGyarfasConjecture}$
   from any valid certificate.
6. A concrete obstruction witness on $K_{3,3}$, formally certifying that it satisfies $\delta(G) \ge 3$
   and contains a 4-cycle ($4 = 2^2$), thus triggering Loud Fail Condition A and precluding $K_{3,3}$
   from serving as a counterexample.
-/

universe u

namespace ErdosGyarfas

/-- A natural number is a valid power-of-two cycle length if $n = 2^k$ for some $k \ge 2$.
    The smallest valid power-of-two cycle length is $2^2 = 4$. -/
def IsPowerOfTwoCycleLength (n : ℕ) : Prop :=
  ∃ k : ℕ, k ≥ 2 ∧ n = 2^k

/-- A simple graph $G$ contains a power-of-two cycle if there exists some vertex $u$
    and a simple cycle $p$ rooted at $u$ whose length is a power of two $\ge 4$. -/
def HasPowerOfTwoCycle {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ IsPowerOfTwoCycleLength p.length

/-- The Erdős–Gyárfás Conjecture (1975):
    Every finite simple graph with minimum degree at least 3 contains a simple cycle
    whose length is a power of two ($2^k$ for $k \ge 2$). -/
def ErdosGyarfasConjecture : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v : V, G.degree v ≥ 3) → HasPowerOfTwoCycle G

/-- A constructive certificate of a counterexample to the Erdős–Gyárfás conjecture:
    an explicit finite graph with minimum degree $\ge 3$ and no simple cycle of power-of-two length. -/
structure CounterexampleCertificate (V : Type u) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  decAdj : DecidableRel G.Adj
  minDeg : ∀ v : V, G.degree v ≥ 3
  noPowerOfTwoCycle : ∀ (u : V) (p : G.Walk u u), p.IsCycle → ¬ IsPowerOfTwoCycleLength p.length

/-- Soundness Meta-Theorem:
    Any valid `CounterexampleCertificate` soundly disproves the Erdős–Gyárfás conjecture. -/
theorem disprove_erdos_gyarfas {V : Type u} [Fintype V] [DecidableEq V]
    (cert : CounterexampleCertificate V) : ¬ ErdosGyarfasConjecture.{u} := by
  intro h
  obtain ⟨u, p, hCycle, hPow⟩ := @h V _ _ cert.G cert.decAdj cert.minDeg
  exact cert.noPowerOfTwoCycle u p hCycle hPow

/-!
### Canonical Cubic Obstruction Witness: $K_{3,3}$

The complete bipartite graph $K_{3,3}$ on 6 vertices has minimum degree 3.
However, $K_{3,3}$ contains 4-cycles ($4 = 2^2$), triggering Loud Fail Condition A:
any candidate graph containing a power-of-two cycle is immediately rejected.
-/

/-- Adjacency in $K_{3,3}$: bipartite partition into $\{0, 1, 2\}$ and $\{3, 4, 5\}$. -/
def K33Adj (u v : Fin 6) : Prop :=
  (u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)

theorem K33Adj.symm {u v : Fin 6} (h : K33Adj u v) : K33Adj v u :=
  h.elim Or.inr Or.inl

theorem K33Adj.loopless (u : Fin 6) (h : K33Adj u u) : False := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The complete bipartite cubic graph $K_{3,3}$ on `Fin 6`. -/
def K33 : SimpleGraph (Fin 6) where
  Adj := K33Adj
  symm := ⟨fun {_ _} h => K33Adj.symm h⟩
  loopless := ⟨K33Adj.loopless⟩

instance : DecidableRel K33.Adj := fun _ _ => by
  dsimp [K33, K33Adj]
  infer_instance

theorem K33_minDeg : ∀ v : Fin 6, K33.degree v ≥ 3 := by
  decide

lemma K33_h01 : K33.Adj (0 : Fin 6) 3 := by decide
lemma K33_h12 : K33.Adj (3 : Fin 6) 1 := by decide
lemma K33_h23 : K33.Adj (1 : Fin 6) 4 := by decide
lemma K33_h30 : K33.Adj (4 : Fin 6) 0 := by decide

/-- Concrete 4-cycle $0 - 3 - 1 - 4 - 0$ in $K_{3,3}$. -/
def K33_cycle : K33.Walk (0 : Fin 6) (0 : Fin 6) :=
  SimpleGraph.Walk.cons K33_h01 (
    SimpleGraph.Walk.cons K33_h12 (
      SimpleGraph.Walk.cons K33_h23 (
        SimpleGraph.Walk.cons K33_h30 SimpleGraph.Walk.nil)))

theorem K33_cycle_length : K33_cycle.length = 4 := rfl

theorem K33_cycle_isCycle : K33_cycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · decide
  · intro h
    contradiction
  · decide

/-- The length of `K33_cycle` is $4 = 2^2$, a power of two with exponent $\ge 2$. -/
theorem K33_cycle_power_of_two : IsPowerOfTwoCycleLength K33_cycle.length := by
  refine ⟨2, by omega, rfl⟩

/-- $K_{3,3}$ contains a power-of-two cycle. -/
theorem K33_hasPowerOfTwoCycle : HasPowerOfTwoCycle K33 :=
  ⟨0, K33_cycle, K33_cycle_isCycle, K33_cycle_power_of_two⟩

/-- Loud Fail Condition A Witness:
    $K_{3,3}$ satisfies the premise $\forall v, \text{degree } v \ge 3$ but fails the
    counterexample condition because it contains an explicit 4-cycle ($4 = 2^2$). -/
theorem K33_fails_counterexample_condition :
    ¬ (∀ (u : Fin 6) (p : K33.Walk u u), p.IsCycle → ¬ IsPowerOfTwoCycleLength p.length) := by
  intro h
  exact h 0 K33_cycle K33_cycle_isCycle K33_cycle_power_of_two

/-- Loud Fail Obstruction Theorem:
    No counterexample certificate can have underlying graph equal to $K_{3,3}$. -/
theorem K33_cannot_be_counterexample (cert : CounterexampleCertificate (Fin 6))
    (hG : cert.G = K33) : False := by
  rcases cert with ⟨G, _decAdj, _minDeg, noPow⟩
  dsimp at hG
  subst hG
  exact noPow 0 K33_cycle K33_cycle_isCycle K33_cycle_power_of_two

end ErdosGyarfas
