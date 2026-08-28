import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

open scoped Matrix BigOperators
open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PicardFuchsMirrorMonodromy

def J : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 0,  0,  1,  0],
    ![ 0,  0,  0,  1],
    ![-1,  0,  0,  0],
    ![ 0, -1,  0,  0]]

def Omega6 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 0,  0,  0,  1],
    ![ 0,  0,  6,  0],
    ![ 0, -6,  0,  0],
    ![-1,  0,  0,  0]]

def T0 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 1, -1,  0,  0],
    ![ 0,  1,  0,  0],
    ![ 0,  0,  1,  0],
    ![ 0,  0,  1,  1]]

def N : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 0, -1,  0,  0],
    ![ 0,  0,  0,  0],
    ![ 0,  0,  0,  0],
    ![ 0,  0,  1,  0]]

theorem N_unipotent_index_2 : N * N = 0 := sorry

namespace ModularFamilyS6

def T0 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 1,  0,  0,  1],
    ![ 0,  1, -1,  0],
    ![ 0,  0,  1,  0],
    ![ 0,  0,  0,  1]]

def N : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 0,  0,  0,  1],
    ![ 0,  0, -1,  0],
    ![ 0,  0,  0,  0],
    ![ 0,  0,  0,  0]]

def gamma : Fin 4 → ℤ := ![1, 0, 0, 0]
def u : Fin 4 → ℤ := ![0, 1, 0, 0]
def w : Fin 4 → ℤ := ![0, 0, 1, 0]
def delta : Fin 4 → ℤ := ![0, 0, 0, 1]

theorem N_act_gamma : N *ᵥ gamma = 0 := sorry
theorem N_act_u : N *ᵥ u = 0 := sorry
theorem N_act_w : N *ᵥ w = -u := sorry
theorem N_act_delta : N *ᵥ delta = gamma := sorry

end ModularFamilyS6

def gamma : Fin 4 → ℤ := ModularFamilyS6.gamma
def u : Fin 4 → ℤ := ModularFamilyS6.u
def w : Fin 4 → ℤ := ModularFamilyS6.w
def delta : Fin 4 → ℤ := ModularFamilyS6.delta

theorem S6_N_act_gamma : ModularFamilyS6.N *ᵥ ModularFamilyS6.gamma = 0 := sorry
theorem S6_N_act_u : ModularFamilyS6.N *ᵥ ModularFamilyS6.u = 0 := sorry
theorem S6_N_act_w : ModularFamilyS6.N *ᵥ ModularFamilyS6.w = -ModularFamilyS6.u := sorry
theorem S6_N_act_delta : ModularFamilyS6.N *ᵥ ModularFamilyS6.delta = ModularFamilyS6.gamma := sorry

def N_MUM : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 0, 1, 0, 0 ],
    ![ 0, 0, 1, 0 ],
    ![ 0, 0, 0, 1 ],
    ![ 0, 0, 0, 0 ]]

def symplecticPairing (v w : Fin 4 → ℤ) : ℤ :=
  v 0 * w 2 + v 1 * w 3 - v 2 * w 0 - v 3 * w 1

theorem symplecticPairing_skew (v w : Fin 4 → ℤ) :
    symplecticPairing v w = -symplecticPairing w v := sorry

theorem mulVec_N (v : Fin 4 → ℤ) :
    N *ᵥ v = ![-v 1, 0, 0, v 2] := sorry

theorem symplecticPairing_N_invariant (v w : Fin 4 → ℤ) :
    symplecticPairing (N *ᵥ v) w + symplecticPairing v (N *ᵥ w) = 0 := sorry

def symplecticPairingOmega6 (v w : Fin 4 → ℤ) : ℤ :=
  v 0 * w 3 + 6 * v 1 * w 2 - 6 * v 2 * w 1 - v 3 * w 0

theorem symplecticPairingOmega6_skew (v w : Fin 4 → ℤ) :
    symplecticPairingOmega6 v w = -symplecticPairingOmega6 w v := sorry

theorem mulVec_S6_N (v : Fin 4 → ℤ) :
    ModularFamilyS6.N *ᵥ v = ![v 3, -v 2, 0, 0] := sorry

theorem symplecticPairingOmega6_N_invariant (v w : Fin 4 → ℤ) :
    symplecticPairingOmega6 (ModularFamilyS6.N *ᵥ v) w +
    symplecticPairingOmega6 v (ModularFamilyS6.N *ᵥ w) = 0 := sorry

end PicardFuchsMirrorMonodromy

namespace UniversalMonodromyWeightFiltration

open Matrix PicardFuchsMirrorMonodromy

/-! ### 1. General Matrix Operator Algebra & Deligne-Schmid Weight Filtration -/

def kerMat {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) : Set (Fin n → R) :=
  {v | M *ᵥ v = 0}

def imMat {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) : Set (Fin n → R) :=
  {v | ∃ u, M *ᵥ u = v}

def imPower {n : ℕ} {R : Type*} [CommRing R] (N : Matrix (Fin n) (Fin n) R) (m : ℤ) : Set (Fin n → R) :=
  if m ≤ 0 then Set.univ else imMat (N ^ m.toNat)

def kerPower {n : ℕ} {R : Type*} [CommRing R] (N : Matrix (Fin n) (Fin n) R) (m : ℕ) : Set (Fin n → R) :=
  kerMat (N ^ m)

def DeligneSummand {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (l : ℕ) (j : ℕ) : Set (Fin n → R) :=
  kerPower N (j + 1) ∩ imPower N ((j : ℤ) - (l : ℤ) + (k : ℤ))

def DeligneWeightSpace {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (l : ℕ) : Set (Fin n → R) :=
  {v | ∃ j : ℕ, j ≤ k ∧ v ∈ DeligneSummand N k l j}

theorem zero_mem_kerPower {n : ℕ} {R : Type*} [CommRing R] (N : Matrix (Fin n) (Fin n) R) (m : ℕ) :
    (0 : Fin n → R) ∈ kerPower N m := sorry

theorem zero_mem_imPower {n : ℕ} {R : Type*} [CommRing R] (N : Matrix (Fin n) (Fin n) R) (m : ℤ) :
    (0 : Fin n → R) ∈ imPower N m := sorry

theorem zero_mem_DeligneSummand {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (l : ℕ) (j : ℕ) :
    (0 : Fin n → R) ∈ DeligneSummand N k l j := sorry

theorem zero_mem_DeligneWeightSpace {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (l : ℕ) :
    (0 : Fin n → R) ∈ DeligneWeightSpace N k l := sorry

theorem imPower_anti {n : ℕ} {R : Type*} [CommRing R] (N : Matrix (Fin n) (Fin n) R)
    (m1 m2 : ℤ) (h : m1 ≤ m2) :
    imPower N m2 ⊆ imPower N m1 := sorry

theorem DeligneSummand_subset_succ {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (l : ℕ) (j : ℕ) :
    DeligneSummand N k l j ⊆ DeligneSummand N k (l + 1) j := sorry

theorem DeligneWeightSpace_subset_succ {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (l : ℕ) :
    DeligneWeightSpace N k l ⊆ DeligneWeightSpace N k (l + 1) := sorry

theorem DeligneWeightSpace_mono {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    ∀ {l1 l2 : ℕ}, l1 ≤ l2 → DeligneWeightSpace N k l1 ⊆ DeligneWeightSpace N k l2 := sorry

theorem N_mulVec_mem_kerPower_pred {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (j : ℕ) (v : Fin n → R)
    (hv : v ∈ kerPower N (j + 1)) :
    N *ᵥ v ∈ kerPower N j := sorry

theorem N_mulVec_mem_imPower_succ {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (m : ℤ) (v : Fin n → R)
    (hv : v ∈ imPower N m) :
    N *ᵥ v ∈ imPower N (m + 1) := sorry

theorem DeligneWeightSpace_top {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (hk : N ^ (k + 1) = 0) (l : ℕ) (hl : 2 * k ≤ l) :
    DeligneWeightSpace N k l = Set.univ := sorry

theorem DeligneWeightSpace_shift {n : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin n) (Fin n) R) (k : ℕ) (l : ℕ) (v : Fin n → R)
    (hv : v ∈ DeligneWeightSpace N k l) :
    N *ᵥ v ∈ DeligneWeightSpace N k (l - 2) := sorry

/-! ### 2. Explicit Computation on $\mathbb{Z}^4$ for $(3,4,\infty)$ Modular Monodromy -/

def W0_34 : Set (Fin 4 → ℤ) := {0}
def W1_34 : Set (Fin 4 → ℤ) := imMat PicardFuchsMirrorMonodromy.N
def W2_34 : Set (Fin 4 → ℤ) := Set.univ

theorem W0_sub_W1 : W0_34 ⊆ W1_34 := sorry
theorem W1_sub_W2 : W1_34 ⊆ W2_34 := sorry

theorem weight_filtration_chain_34 : W0_34 ⊆ W1_34 ∧ W1_34 ⊆ W2_34 := sorry

theorem N_act_W1_in_W0 (v : Fin 4 → ℤ) (hv : v ∈ W1_34) :
    PicardFuchsMirrorMonodromy.N *ᵥ v ∈ W0_34 := sorry

theorem N_act_W2_in_W1 (v : Fin 4 → ℤ) (_hv : v ∈ W2_34) :
    PicardFuchsMirrorMonodromy.N *ᵥ v ∈ W1_34 := sorry

theorem N_act_W2_in_W0 (v : Fin 4 → ℤ) (hv : v ∈ W2_34) :
    PicardFuchsMirrorMonodromy.N *ᵥ (PicardFuchsMirrorMonodromy.N *ᵥ v) ∈ W0_34 := sorry

theorem N_act_gamma : PicardFuchsMirrorMonodromy.N *ᵥ PicardFuchsMirrorMonodromy.gamma = 0 := sorry

theorem N_act_u :
    PicardFuchsMirrorMonodromy.N *ᵥ PicardFuchsMirrorMonodromy.u =
    -PicardFuchsMirrorMonodromy.gamma := sorry

theorem N_act_w :
    PicardFuchsMirrorMonodromy.N *ᵥ PicardFuchsMirrorMonodromy.w =
    PicardFuchsMirrorMonodromy.delta := sorry

theorem N_act_delta : PicardFuchsMirrorMonodromy.N *ᵥ PicardFuchsMirrorMonodromy.delta = 0 := sorry

theorem S6_N_act_gamma : ModularFamilyS6.N *ᵥ PicardFuchsMirrorMonodromy.gamma = 0 := sorry
theorem S6_N_act_u : ModularFamilyS6.N *ᵥ PicardFuchsMirrorMonodromy.u = 0 := sorry
theorem S6_N_act_w :
    ModularFamilyS6.N *ᵥ PicardFuchsMirrorMonodromy.w = -PicardFuchsMirrorMonodromy.u := sorry
theorem S6_N_act_delta :
    ModularFamilyS6.N *ᵥ PicardFuchsMirrorMonodromy.delta = PicardFuchsMirrorMonodromy.gamma := sorry

/-! ### 3. Explicit Computation for Type III MUM Monodromy -/

def W_MUM_0 : Set (Fin 4 → ℤ) := {0}
def W_MUM_1 : Set (Fin 4 → ℤ) := {v | v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0}
def W_MUM_2 : Set (Fin 4 → ℤ) := {v | v 2 = 0 ∧ v 3 = 0}
def W_MUM_3 : Set (Fin 4 → ℤ) := {v | v 3 = 0}
def W_MUM_4 : Set (Fin 4 → ℤ) := Set.univ

theorem W_MUM_chain_0_1 : W_MUM_0 ⊆ W_MUM_1 := sorry
theorem W_MUM_chain_1_2 : W_MUM_1 ⊆ W_MUM_2 := sorry
theorem W_MUM_chain_2_3 : W_MUM_2 ⊆ W_MUM_3 := sorry
theorem W_MUM_chain_3_4 : W_MUM_3 ⊆ W_MUM_4 := sorry

theorem W_MUM_complete_chain :
    W_MUM_0 ⊆ W_MUM_1 ∧ W_MUM_1 ⊆ W_MUM_2 ∧ W_MUM_2 ⊆ W_MUM_3 ∧ W_MUM_3 ⊆ W_MUM_4 := sorry

theorem mulVec_N_MUM (v : Fin 4 → ℤ) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ v = ![v 1, v 2, v 3, 0] := sorry

theorem N_MUM_act_W0 (v : Fin 4 → ℤ) (hv : v ∈ W_MUM_0) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ v ∈ W_MUM_0 := sorry

theorem N_MUM_act_W1 (v : Fin 4 → ℤ) (hv : v ∈ W_MUM_1) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ v ∈ W_MUM_0 := sorry

theorem N_MUM_act_W2 (v : Fin 4 → ℤ) (hv : v ∈ W_MUM_2) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ v ∈ W_MUM_1 := sorry

theorem N_MUM_act_W3 (v : Fin 4 → ℤ) (hv : v ∈ W_MUM_3) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ v ∈ W_MUM_2 := sorry

theorem N_MUM_act_W4 (v : Fin 4 → ℤ) (_hv : v ∈ W_MUM_4) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ v ∈ W_MUM_3 := sorry

theorem N_MUM_shift_2_0 (v : Fin 4 → ℤ) (hv : v ∈ W_MUM_2) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ (PicardFuchsMirrorMonodromy.N_MUM *ᵥ v) ∈ W_MUM_0 := sorry

theorem N_MUM_shift_3_1 (v : Fin 4 → ℤ) (hv : v ∈ W_MUM_3) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ (PicardFuchsMirrorMonodromy.N_MUM *ᵥ v) ∈ W_MUM_1 := sorry

theorem N_MUM_shift_4_2 (v : Fin 4 → ℤ) (hv : v ∈ W_MUM_4) :
    PicardFuchsMirrorMonodromy.N_MUM *ᵥ (PicardFuchsMirrorMonodromy.N_MUM *ᵥ v) ∈ W_MUM_2 := sorry

/-! ### 4. Hodge-Riemann Symplectic Polarization & Infinitesimal Isometry -/

theorem J_N_plus_NT_J_zero :
    PicardFuchsMirrorMonodromy.J * PicardFuchsMirrorMonodromy.N +
    PicardFuchsMirrorMonodromy.Nᵀ * PicardFuchsMirrorMonodromy.J = 0 := sorry

theorem NT_J_plus_J_N_zero :
    PicardFuchsMirrorMonodromy.Nᵀ * PicardFuchsMirrorMonodromy.J +
    PicardFuchsMirrorMonodromy.J * PicardFuchsMirrorMonodromy.N = 0 := sorry

def Q_N (v w : Fin 4 → ℤ) : ℤ :=
  PicardFuchsMirrorMonodromy.symplecticPairing v (PicardFuchsMirrorMonodromy.N *ᵥ w)

theorem Q_N_symm (v w : Fin 4 → ℤ) : Q_N v w = Q_N w v := sorry

theorem Q_N_u_w :
    Q_N PicardFuchsMirrorMonodromy.u PicardFuchsMirrorMonodromy.w = 1 := sorry

theorem Q_N_w_u :
    Q_N PicardFuchsMirrorMonodromy.w PicardFuchsMirrorMonodromy.u = 1 := sorry

theorem Q_N_u_u :
    Q_N PicardFuchsMirrorMonodromy.u PicardFuchsMirrorMonodromy.u = 0 := sorry

theorem Q_N_w_w :
    Q_N PicardFuchsMirrorMonodromy.w PicardFuchsMirrorMonodromy.w = 0 := sorry

theorem Q_N_u_add_w_eval :
    Q_N (PicardFuchsMirrorMonodromy.u + PicardFuchsMirrorMonodromy.w)
        (PicardFuchsMirrorMonodromy.u + PicardFuchsMirrorMonodromy.w) = 2 := sorry

theorem Q_N_u_add_w_strictly_positive :
    0 < Q_N (PicardFuchsMirrorMonodromy.u + PicardFuchsMirrorMonodromy.w)
            (PicardFuchsMirrorMonodromy.u + PicardFuchsMirrorMonodromy.w) := sorry

def Q_N_S6 (v w : Fin 4 → ℤ) : ℤ :=
  symplecticPairingOmega6 v (ModularFamilyS6.N *ᵥ w)

theorem Q_N_S6_symm (v w : Fin 4 → ℤ) : Q_N_S6 v w = Q_N_S6 w v := sorry

theorem Q_N_S6_w_pos :
    Q_N_S6 w w = 6 := sorry

theorem Q_N_S6_w_strictly_positive :
    0 < Q_N_S6 w w := sorry

theorem Q_N_S6_delta_eval :
    Q_N_S6 delta delta = -1 := sorry

theorem Q_N_S6_delta_nondegenerate :
    Q_N_S6 delta delta ≠ 0 := sorry

end UniversalMonodromyWeightFiltration
