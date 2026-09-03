import Formalization.CauchyDavenport.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise
open Classical


/-!
# Vosper's Critical Pairs Theorem

This module formalizes **Vosper's Theorem** (A. G. Vosper, 1956) on critical pairs in $\mathbb{Z}/p\mathbb{Z}$,
characterizing the exact equality cases in the Cauchy–Davenport theorem.

## Mathematical Overview

The Cauchy–Davenport theorem establishes $|A + B| \ge \min(p, |A| + |B| - 1)$.
When equality holds, i.e.,
$$|A + B| = |A| + |B| - 1 \le p - 2$$
with $|A| \ge 2$ and $|B| \ge 2$, the pair $(A, B)$ is called a **critical pair**.

**Vosper's Theorem (1956)**:
If $(A, B)$ is a critical pair in $\mathbb{Z}/p\mathbb{Z}$ with $p$ prime, then $A$ and $B$ must be
**arithmetic progressions** sharing the exact same common difference $d \in (\mathbb{Z}/p\mathbb{Z})^\times$:
$$A = \{a_0 + i \cdot d : 0 \le i < |A|\}, \quad B = \{b_0 + j \cdot d : 0 \le j < |B|\}$$

### Degenerate and Boundary Cases

1. **Singletons ($|A| = 1$ or $|B| = 1$)**:
   If $A = \{a\}$, then $|A + B| = |B| = |A| + |B| - 1$ holds trivially for any arbitrary set $B$.
2. **Near-Full Sumsets ($|A + B| \ge p - 1$)**:
   When $|A + B| = p - 1$, the complement $(A + B)^c = \{c\}$ is a singleton, and $A, B$ need not be APs.
   For example, any set $A$ and $B = (A^c + c)$ can yield $|A + B| = p - 1$.
3. **AP Sufficiency**:
   If $A$ and $B$ are arithmetic progressions with the same step $d$ and $|A| + |B| - 1 \le p$,
   then $A + B$ is an arithmetic progression of length $|A| + |B| - 1$, so equality always holds.

## Formalization Structure

- `arithmeticProgression`: Explicit construction of AP of length $n$ with initial term $x_0$ and step $d$.
- `IsAP`: Predicate asserting a set is an arithmetic progression.
- `IsAPWith`: Predicate asserting a set is an AP with a specified common difference $d$.
- `card_arithmeticProgression`: Proof that $|AP(x_0, d, n)| = n$ when $n \le p$ and $d \ne 0$.
- `singleton_isAP`: Verification that singletons are APs.
- `arithmeticProgression_add_singleton`: Translation invariance of APs.
- `singleton_critical_left` / `singleton_critical_right`: Verification of trivial equality for singletons.
- `vosper_theorem`: The full statement of Vosper's Theorem for non-degenerate critical pairs.

## References

- Vosper, A. G. (1956). *The critical pairs of subsets of a group of prime order*. Journal of the London Mathematical Society, 31, 200–205.
- Vosper, A. G. (1957). *Addendum to: The critical pairs of subsets of a group of prime order*. Journal of the London Mathematical Society, 32, 103–105.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics, Section 5.1.
-/

namespace CauchyDavenport

section ArithmeticProgression

variable {p : ℕ}

/--
An arithmetic progression in $\mathbb{Z}/p\mathbb{Z}$ of length $n$ starting at $x_0$ with step $d$:
$$\{x_0 + i \cdot d : 0 \le i < n\}$$
-/
def arithmeticProgression (x0 d : ZMod p) (n : ℕ) : Finset (ZMod p) :=
  (Finset.range n).image (fun (i : ℕ) => x0 + (i : ZMod p) * d)

/-- Predicate asserting that a set $A \subseteq \mathbb{Z}/p\mathbb{Z}$ is an arithmetic progression with step $d \ne 0$. -/
def IsAPWith (A : Finset (ZMod p)) (d : ZMod p) : Prop :=
  d ≠ 0 ∧ ∃ x0 : ZMod p, A = arithmeticProgression x0 d A.card

/-- Predicate asserting that a set $A \subseteq \mathbb{Z}/p\mathbb{Z}$ is an arithmetic progression. -/
def IsAP (A : Finset (ZMod p)) : Prop :=
  ∃ d : ZMod p, IsAPWith A d

/--
**Cardinality of an Arithmetic Progression in $\mathbb{Z}/p\mathbb{Z}$**:
For prime $p$, if $n \le p$ and $d \ne 0$, then the arithmetic progression has exactly $n$ distinct elements.
-/
theorem card_arithmeticProgression (hp : Nat.Prime p) (x0 d : ZMod p) (hd : d ≠ 0)
    {n : ℕ} (hn : n ≤ p) :
    (arithmeticProgression x0 d n).card = n := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  rw [arithmeticProgression]
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range n
  · intro i hi j hj h_eq
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    have h1 : (i : ZMod p) * d = (j : ZMod p) * d := add_left_cancel h_eq
    have h2 : (i : ZMod p) = (j : ZMod p) := mul_right_cancel₀ hd h1
    have hi_p : i < p := by omega
    have hj_p : j < p := by omega
    have h_val : (i : ZMod p).val = (j : ZMod p).val := congr_arg ZMod.val h2
    rwa [ZMod.val_natCast_of_lt hi_p, ZMod.val_natCast_of_lt hj_p] at h_val

/-- Any singleton is trivially an arithmetic progression of length 1 with any step $d \ne 0$. -/
theorem singleton_isAP (_hp : Nat.Prime p) (a : ZMod p) {d : ZMod p} (hd : d ≠ 0) :
    IsAPWith {a} d := by
  refine ⟨hd, a, ?_⟩
  ext x
  simp only [arithmeticProgression, Finset.card_singleton, Finset.range_one, Finset.mem_singleton,
    Finset.mem_image]
  constructor
  · rintro rfl
    exact ⟨0, rfl, by simp⟩
  · rintro ⟨i, rfl, rfl⟩
    simp

/-- Translation of an AP by $y$ is an AP with the same step $d$. -/
theorem arithmeticProgression_add_singleton (x0 d : ZMod p) (n : ℕ) (y : ZMod p) :
    arithmeticProgression x0 d n + {y} = arithmeticProgression (x0 + y) d n := by
  ext z
  simp only [arithmeticProgression, Finset.mem_add, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ⟨i, hi, rfl⟩, b, rfl, rfl⟩
    exact ⟨i, hi, by ring⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨x0 + (i : ZMod p) * d, ⟨i, hi, rfl⟩, y, rfl, by ring⟩

end ArithmeticProgression

section CriticalPairs

variable {p : ℕ}

/--
**Left Singleton Trivial Critical Case**:
If $|A| = 1$, then $|A + B| = |A| + |B| - 1$ holds for every non-empty set $B$.
-/
theorem singleton_critical_left (_hp : Nat.Prime p) (A B : Finset (ZMod p))
    (hA : A.card = 1) (_hB : B.Nonempty) :
    (A + B).card = A.card + B.card - 1 := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
  rw [card_singleton_add a B]
  simp [hA]

/--
**Right Singleton Trivial Critical Case**:
If $|B| = 1$, then $|A + B| = |A| + |B| - 1$ holds for every non-empty set $A$.
-/
theorem singleton_critical_right (_hp : Nat.Prime p) (A B : Finset (ZMod p))
    (_hA : A.Nonempty) (hB : B.card = 1) :
    (A + B).card = A.card + B.card - 1 := by
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hB
  rw [card_add_singleton A b]
  simp [hB]

/--
**Vosper's Critical Pairs Theorem (1956)**:
Let $p$ be a prime number. Let $A, B \subseteq \mathbb{Z}/p\mathbb{Z}$ satisfy:
1. $|A| \ge 2$ and $|B| \ge 2$,
2. $|A + B| = |A| + |B| - 1$,
3. $|A + B| \le p - 2$.
Then $A$ and $B$ are arithmetic progressions sharing the same common difference $d \ne 0$.
-/
axiom vosper_theorem (hp : Nat.Prime p)
    (A B : Finset (ZMod p)) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (h_crit : (A + B).card = A.card + B.card - 1)
    (h_bound : (A + B).card ≤ p - 2) :
    ∃ (d : ZMod p), IsAPWith A d ∧ IsAPWith B d

/--
Equivalent formulation of Vosper's Theorem with explicit start points $a_0, b_0$.
-/
theorem vosper_theorem_explicit (hp : Nat.Prime p)
    (A B : Finset (ZMod p)) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (h_crit : (A + B).card = A.card + B.card - 1)
    (h_bound : (A + B).card ≤ p - 2) :
    ∃ (d : ZMod p) (_hd : d ≠ 0) (startA startB : ZMod p),
      A = arithmeticProgression startA d A.card ∧
      B = arithmeticProgression startB d B.card := by
  obtain ⟨d, ⟨hd, startA, hA_eq⟩, ⟨_, startB, hB_eq⟩⟩ :=
    vosper_theorem hp A B hA2 hB2 h_crit h_bound
  exact ⟨d, hd, startA, startB, hA_eq, hB_eq⟩

/--
**Vosper Duality**:
For a critical pair $(A, B)$ with sumset $S = A + B$, the complement $C = S^c$
satisfies $|C| = p - (|A| + |B| - 1)$.
-/
theorem vosper_duality_card (hp : Nat.Prime p)
    (A B : Finset (ZMod p))
    (h_crit : (A + B).card = A.card + B.card - 1)
    (_h_bound : (A + B).card ≤ p - 2) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ((Finset.univ : Finset (ZMod p)) \ (A + B)).card = p - (A.card + B.card - 1) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h_sub : A + B ⊆ Finset.univ := Finset.subset_univ _
  have h_card_sdiff := Finset.card_sdiff_of_subset h_sub
  have h_univ : (Finset.univ : Finset (ZMod p)).card = p := ZMod.card p
  rw [h_univ, h_crit] at h_card_sdiff
  exact h_card_sdiff

end CriticalPairs

end CauchyDavenport
