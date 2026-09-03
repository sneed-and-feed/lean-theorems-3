/-
Copyright (c) 2026 Lean Theorems Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Theorems Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# The Lonely Runner Conjecture at k = 8 with Loud Fail Verification

The Lonely Runner Conjecture, first posed by Jörg M. Wills (1967) in Diophantine approximation
and independently by Thomas W. Cusick (1974) as a view-obstruction problem in geometry of numbers,
asserts that if $k$ runners run on a circular track of unit length with distinct constant speeds,
each runner will eventually be at distance at least $1 / (k + 1)$ from all other runners.
In relative terms (fixing one runner as stationary at the origin), $k$ runners with distinct
positive integer speeds $v_1, \dots, v_k$ satisfy that there exists $t > 0$ such that every runner
is "lonely", i.e., distance to the nearest integer is at least $1 / (k + 1)$.

In September 2025, Matthieu Rosenfeld (arXiv:2509.14111) proved that the conjecture holds for
$k = 8$ runners (and subsequently for $k = 9$ runners).

This module formalizes:
1. `IsFarFromInt`: distance predicate measuring separation from all integers $\ge \delta$.
2. `IsLonely`: runner isolation predicate at time $t$ with separation $\delta$.
3. `lonelyThreshold`: canonical isolation bound $1 / (k + 1)$.
4. `lonelyThreshold_eight`: evaluation $\text{lonelyThreshold}(8) = 1/9$.
5. `LonelyRunnerConjecture`: general $k$-dimensional conjecture.
6. `LonelyRunnerConjecture8`: specialization to dimension $k = 8$.
7. `CounterexampleCertificate8`: constructive certificate structure for a potential counterexample.
8. `disprove_lonely_runner_8`: sound meta-theorem deriving $\neg \text{LonelyRunnerConjecture8}$.
9. `canonicalSpeeds8`: canonical consecutive integer speeds $v_i = i + 1$ for $i \in \{0, \dots, 7\}$.
10. `canonicalSpeeds8_pos`, `canonicalSpeeds8_inj`: structural invariants.
11. `canonicalSpeeds8_lonely_at_one_ninth`: simultaneous loneliness of all 8 runners at $t = 1/9$.
12. `canonicalSpeeds8_fails_counterexample_condition`: Loud Fail Condition A witness.
13. `canonicalSpeeds8_cannot_be_counterexample`: Loud Fail Obstruction Theorem.
-/

namespace LonelyRunner8

/-- A real number $x$ is at distance at least $\delta$ from every integer. -/
def IsFarFromInt (x : ℝ) (δ : ℝ) : Prop := ∀ m : ℤ, |x - (m : ℝ)| ≥ δ

/-- A runner with speed $v \in \mathbb{N}$ is lonely at time $t \in \mathbb{R}$ with separation $\delta$
    if the position $t \cdot v$ is at distance at least $\delta$ from every integer. -/
def IsLonely (v : ℕ) (t : ℝ) (δ : ℝ) : Prop := IsFarFromInt (t * (v : ℝ)) δ

/-- The canonical lonely threshold for $k$ runners is $1 / (k + 1)$. -/
noncomputable def lonelyThreshold (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- For $k = 8$ runners, the canonical loneliness threshold is $1 / 9$. -/
theorem lonelyThreshold_eight : lonelyThreshold 8 = 1 / 9 := by
  norm_num [lonelyThreshold]

/-- The Lonely Runner Conjecture for $k$ runners:
    For any $k$ distinct strictly positive integer speeds, there exists a time $t > 0$
    at which every runner is at distance at least $1 / (k + 1)$ from every integer. -/
def LonelyRunnerConjecture (k : ℕ) : Prop :=
  ∀ (v : Fin k → ℕ), (∀ i, 0 < v i) → Function.Injective v →
    ∃ t : ℝ, t > 0 ∧ ∀ i : Fin k, IsLonely (v i) t (lonelyThreshold k)

/-- Specialization of the Lonely Runner Conjecture to $k = 8$ runners. -/
def LonelyRunnerConjecture8 : Prop := LonelyRunnerConjecture 8

/-- A constructive certificate of a counterexample to the Lonely Runner Conjecture at $k = 8$:
    an explicit set of 8 distinct positive speeds such that at no positive time $t > 0$
    are all 8 runners simultaneously lonely with threshold $1 / 9$. -/
structure CounterexampleCertificate8 where
  speeds : Fin 8 → ℕ
  pos : ∀ i : Fin 8, 0 < speeds i
  inj : Function.Injective speeds
  not_lonely : ∀ t : ℝ, t > 0 → ¬ (∀ i : Fin 8, IsLonely (speeds i) t (1 / 9 : ℝ))

/-- Soundness Meta-Theorem:
    Any valid `CounterexampleCertificate8` soundly disproves `LonelyRunnerConjecture8`. -/
theorem disprove_lonely_runner_8 (cert : CounterexampleCertificate8) :
    ¬ LonelyRunnerConjecture8 := fun h => by
  rcases h cert.speeds cert.pos cert.inj with ⟨t, ht, hl⟩
  exact cert.not_lonely t ht (lonelyThreshold_eight ▸ hl)

/-- Canonical candidate speed assignment for $k = 8$: consecutive integers $1, 2, \dots, 8$. -/
def canonicalSpeeds8 : Fin 8 → ℕ := fun i => i.val + 1

/-- Every speed in `canonicalSpeeds8` is strictly positive. -/
theorem canonicalSpeeds8_pos (i : Fin 8) : 0 < canonicalSpeeds8 i :=
  Nat.succ_pos _

/-- The canonical speed assignment `canonicalSpeeds8` is injective. -/
theorem canonicalSpeeds8_inj : Function.Injective canonicalSpeeds8 :=
  fun _ _ h => Fin.ext (Nat.succ.inj h)

/-- At time $t = 1 / 9$, every runner in `canonicalSpeeds8` is simultaneously lonely
    with separation threshold $1 / 9$. -/
theorem canonicalSpeeds8_lonely_at_one_ninth (i : Fin 8) :
    IsLonely (canonicalSpeeds8 i) (1 / 9 : ℝ) (1 / 9 : ℝ) := by
  intro m
  dsimp [IsLonely, IsFarFromInt, canonicalSpeeds8]
  push_cast
  have hi_le : (i.val : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hi_ge : (i.val : ℝ) ≥ 0 := Nat.cast_nonneg i.val
  rw [ge_iff_le, le_abs]
  rcases le_or_gt 1 m with hm1 | hm0
  · have : (m : ℝ) ≥ 1 := by exact_mod_cast hm1
    right; linarith
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast (show m ≤ 0 by omega)
    left; linarith

/-- Loud Fail Condition A Witness:
    The canonical speed assignment `canonicalSpeeds8` fails the counterexample condition
    because at $t = 1 / 9 > 0$, all 8 runners are simultaneously lonely. -/
theorem canonicalSpeeds8_fails_counterexample_condition :
    ¬ (∀ t : ℝ, t > 0 → ¬ (∀ i : Fin 8, IsLonely (canonicalSpeeds8 i) t (1 / 9 : ℝ))) :=
  fun h => h (1 / 9) (by norm_num) canonicalSpeeds8_lonely_at_one_ninth

/-- Loud Fail Obstruction Theorem:
    No counterexample certificate can have speeds equal to `canonicalSpeeds8`. -/
theorem canonicalSpeeds8_cannot_be_counterexample
    (cert : CounterexampleCertificate8) (h : cert.speeds = canonicalSpeeds8) : False := by
  obtain ⟨_, _, _, not_lonely⟩ := cert
  subst h
  exact not_lonely (1 / 9) (by norm_num) canonicalSpeeds8_lonely_at_one_ninth

end LonelyRunner8
