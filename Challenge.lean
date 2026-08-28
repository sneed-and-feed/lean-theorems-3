import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
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

/-! ### 1. Picard-Fuchs Differential Operator $\mathcal{L}_4$ & Hypergeometric Parameters -/

def e1 (α : Fin 4 → ℚ) : ℚ :=
  α 0 + α 1 + α 2 + α 3

def e2 (α : Fin 4 → ℚ) : ℚ :=
  α 0 * α 1 + α 0 * α 2 + α 0 * α 3 + α 1 * α 2 + α 1 * α 3 + α 2 * α 3

def e3 (α : Fin 4 → ℚ) : ℚ :=
  α 0 * α 1 * α 2 + α 0 * α 1 * α 3 + α 0 * α 2 * α 3 + α 1 * α 2 * α 3

def e4 (α : Fin 4 → ℚ) : ℚ :=
  α 0 * α 1 * α 2 * α 3

def pfSymbol (α : Fin 4 → ℚ) (z θ : ℚ) : ℚ :=
  θ^4 - z * (θ + α 0) * (θ + α 1) * (θ + α 2) * (θ + α 3)

theorem pfSymbol_expansion (α : Fin 4 → ℚ) (z θ : ℚ) :
    pfSymbol α z θ = (1 - z) * θ^4 - z * (e1 α * θ^3 + e2 α * θ^2 + e3 α * θ + e4 α) := sorry

def alpha_3_4_infty : Fin 4 → ℚ :=
  ![1/12, 5/12, 7/12, 11/12]

def alpha_3_4_geom : Fin 4 → ℚ :=
  alpha_3_4_infty

def alpha_3_4_mod : Fin 4 → ℚ :=
  ![1/3, 2/3, 1/4, 3/4]

def alpha_2_3_infty : Fin 4 → ℚ :=
  ![1/6, 5/6, 1/6, 5/6]

def alpha_2_3 : Fin 4 → ℚ :=
  alpha_2_3_infty

theorem sum_alpha_3_4_infty : (∑ i : Fin 4, alpha_3_4_infty i) = 2 := sorry
theorem e1_alpha_3_4_infty : e1 alpha_3_4_infty = 2 := sorry
theorem e1_alpha_3_4_geom : e1 alpha_3_4_geom = 2 := sorry
theorem sum_alpha_3_4_geom : (∑ i : Fin 4, alpha_3_4_geom i) = 2 := sorry
theorem e2_alpha_3_4_infty : e2 alpha_3_4_infty = 95 / 72 := sorry
theorem e2_alpha_3_4_geom : e2 alpha_3_4_geom = 95 / 72 := sorry
theorem e3_alpha_3_4_infty : e3 alpha_3_4_infty = 23 / 72 := sorry
theorem e3_alpha_3_4_geom : e3 alpha_3_4_geom = 23 / 72 := sorry
theorem e4_alpha_3_4_infty : e4 alpha_3_4_infty = 385 / 20736 := sorry
theorem e4_alpha_3_4_geom : e4 alpha_3_4_geom = 385 / 20736 := sorry

theorem sum_alpha_3_4_mod : (∑ i : Fin 4, alpha_3_4_mod i) = 2 := sorry
theorem e1_alpha_3_4_mod : e1 alpha_3_4_mod = 2 := sorry
theorem e2_alpha_3_4_mod : e2 alpha_3_4_mod = 203 / 144 := sorry
theorem e3_alpha_3_4_mod : e3 alpha_3_4_mod = 59 / 144 := sorry
theorem e4_alpha_3_4_mod : e4 alpha_3_4_mod = 1 / 24 := sorry

theorem sum_alpha_2_3_infty : (∑ i : Fin 4, alpha_2_3_infty i) = 2 := sorry
theorem e1_alpha_2_3_infty : e1 alpha_2_3_infty = 2 := sorry
theorem e1_alpha_2_3 : e1 alpha_2_3 = 2 := sorry
theorem e2_alpha_2_3_infty : e2 alpha_2_3_infty = 23 / 18 := sorry
theorem e2_alpha_2_3 : e2 alpha_2_3 = 23 / 18 := sorry
theorem e3_alpha_2_3_infty : e3 alpha_2_3_infty = 5 / 18 := sorry
theorem e3_alpha_2_3 : e3 alpha_2_3 = 5 / 18 := sorry
theorem e4_alpha_2_3_infty : e4 alpha_2_3_infty = 25 / 1296 := sorry
theorem e4_alpha_2_3 : e4 alpha_2_3 = 25 / 1296 := sorry

def indicialPoly (α : Fin 4 → ℚ) (θ : ℚ) : ℚ :=
  pfSymbol α 0 θ

theorem indicialPoly_eq (α : Fin 4 → ℚ) (θ : ℚ) : indicialPoly α θ = θ^4 := sorry
theorem indicialPoly_zero (α : Fin 4 → ℚ) : indicialPoly α 0 = 0 := sorry
theorem indicial_root_unique (α : Fin 4 → ℚ) (θ : ℚ) (h : indicialPoly α θ = 0) : θ = 0 := sorry

/-! ### 2. Frobenius Local Monodromy at Cusp $z = 0$ -/

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

theorem N_eq_T0_sub_one : N = T0 - 1 := sorry
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

theorem N_def : N = T0 - 1 := sorry
theorem N_squared_zero : N * N = 0 := sorry

def gamma : Fin 4 → ℤ := ![1, 0, 0, 0]
def u : Fin 4 → ℤ := ![0, 1, 0, 0]
def w : Fin 4 → ℤ := ![0, 0, 1, 0]
def delta : Fin 4 → ℤ := ![0, 0, 0, 1]

theorem N_act_gamma : N *ᵥ gamma = 0 := sorry
theorem N_act_u : N *ᵥ u = 0 := sorry
theorem N_act_w : N *ᵥ w = -u := sorry
theorem N_act_delta : N *ᵥ delta = gamma := sorry

end ModularFamilyS6

theorem ModularFamilyS6_N_eq_T0_sub_one : ModularFamilyS6.N = ModularFamilyS6.T0 - 1 := sorry
theorem ModularFamilyS6_N_unipotent_index_2 : ModularFamilyS6.N * ModularFamilyS6.N = 0 := sorry

def gamma : Fin 4 → ℤ := ModularFamilyS6.gamma
def u : Fin 4 → ℤ := ModularFamilyS6.u
def w : Fin 4 → ℤ := ModularFamilyS6.w
def delta : Fin 4 → ℤ := ModularFamilyS6.delta

theorem S6_N_act_gamma : ModularFamilyS6.N *ᵥ ModularFamilyS6.gamma = 0 := sorry
theorem S6_N_act_u : ModularFamilyS6.N *ᵥ ModularFamilyS6.u = 0 := sorry
theorem S6_N_act_w : ModularFamilyS6.N *ᵥ ModularFamilyS6.w = -ModularFamilyS6.u := sorry
theorem S6_N_act_delta : ModularFamilyS6.N *ᵥ ModularFamilyS6.delta = ModularFamilyS6.gamma := sorry

theorem N_act_gamma : ModularFamilyS6.N *ᵥ gamma = 0 := sorry
theorem N_act_u : ModularFamilyS6.N *ᵥ u = 0 := sorry
theorem N_act_w : ModularFamilyS6.N *ᵥ w = -u := sorry
theorem N_act_delta : ModularFamilyS6.N *ᵥ delta = gamma := sorry

theorem N_act_e0 : N *ᵥ ![1, 0, 0, 0] = 0 := sorry
theorem N_act_e1 : N *ᵥ ![0, 1, 0, 0] = ![-1, 0, 0, 0] := sorry
theorem N_act_e2 : N *ᵥ ![0, 0, 1, 0] = ![0, 0, 0, 1] := sorry
theorem N_act_e3 : N *ᵥ ![0, 0, 0, 1] = 0 := sorry

theorem mulVec_N (v : Fin 4 → ℤ) :
    N *ᵥ v = ![-v 1, 0, 0, v 2] := sorry

theorem mulVec_T0 (v : Fin 4 → ℤ) :
    T0 *ᵥ v = ![v 0 - v 1, v 1, v 2, v 2 + v 3] := sorry

theorem mulVec_S6_N (v : Fin 4 → ℤ) :
    ModularFamilyS6.N *ᵥ v = ![v 3, -v 2, 0, 0] := sorry

theorem mulVec_S6_T0 (v : Fin 4 → ℤ) :
    ModularFamilyS6.T0 *ᵥ v = ![v 0 + v 3, v 1 - v 2, v 2, v 3] := sorry

def N_MUM : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 0, 1, 0, 0 ],
    ![ 0, 0, 1, 0 ],
    ![ 0, 0, 0, 1 ],
    ![ 0, 0, 0, 0 ]]

def IsTypeII (M : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  M ≠ 0 ∧ M * M = 0

def IsTypeIII (M : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  M * M ≠ 0 ∧ M * M * M * M = 0

theorem typeII_not_typeIII (M : Matrix (Fin 4) (Fin 4) ℤ) (h : IsTypeII M) : ¬ IsTypeIII M := sorry
theorem N_MUM_squared_ne_zero : N_MUM * N_MUM ≠ 0 := sorry
theorem N_MUM_cubed_ne_zero : N_MUM * N_MUM * N_MUM ≠ 0 := sorry
theorem N_MUM_fourth_zero : N_MUM * N_MUM * N_MUM * N_MUM = 0 := sorry
theorem N_MUM_is_typeIII : IsTypeIII N_MUM := sorry
theorem N_is_typeII : IsTypeII N := sorry
theorem N_not_typeIII : ¬ IsTypeIII N := sorry
theorem ModularFamilyS6_N_is_typeII : IsTypeII ModularFamilyS6.N := sorry
theorem ModularFamilyS6_N_not_typeIII : ¬ IsTypeIII ModularFamilyS6.N := sorry

/-! ### 3. Symplectic Bilinear Invariance & Griffiths Transversality -/

def IsSymplectic (M : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  Mᵀ * J * M = J

def IsInfinitesimalSymplectic (M : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  Mᵀ * J + J * M = 0

def IsInfinitesimalSymplecticOmega6 (M : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  Mᵀ * Omega6 + Omega6 * M = 0

theorem isInfinitesimalSymplectic_N : IsInfinitesimalSymplectic N := sorry
theorem isInfinitesimalSymplectic_S6_N : IsInfinitesimalSymplecticOmega6 ModularFamilyS6.N := sorry
theorem isSymplectic_T0 : IsSymplectic T0 := sorry
theorem isSymplectic_S6_T0 :
    ModularFamilyS6.T0ᵀ * Omega6 * ModularFamilyS6.T0 = Omega6 := sorry

def symplecticPairing (v w : Fin 4 → ℤ) : ℤ :=
  v 0 * w 2 + v 1 * w 3 - v 2 * w 0 - v 3 * w 1

theorem symplecticPairing_def (v w : Fin 4 → ℤ) :
    symplecticPairing v w = v 0 * w 2 + v 1 * w 3 - v 2 * w 0 - v 3 * w 1 := sorry

theorem symplecticPairing_skew (v w : Fin 4 → ℤ) :
    symplecticPairing v w = -symplecticPairing w v := sorry

theorem symplecticPairing_self_zero (v : Fin 4 → ℤ) :
    symplecticPairing v v = 0 := sorry

theorem symplecticPairing_N_invariant (v w : Fin 4 → ℤ) :
    symplecticPairing (N *ᵥ v) w + symplecticPairing v (N *ᵥ w) = 0 := sorry

theorem symplecticPairing_T0_invariant (v w : Fin 4 → ℤ) :
    symplecticPairing (T0 *ᵥ v) (T0 *ᵥ w) = symplecticPairing v w := sorry

def symplecticPairingOmega6 (v w : Fin 4 → ℤ) : ℤ :=
  v 0 * w 3 + 6 * v 1 * w 2 - 6 * v 2 * w 1 - v 3 * w 0

theorem symplecticPairingOmega6_def (v w : Fin 4 → ℤ) :
    symplecticPairingOmega6 v w = v 0 * w 3 + 6 * v 1 * w 2 - 6 * v 2 * w 1 - v 3 * w 0 := sorry

theorem symplecticPairingOmega6_skew (v w : Fin 4 → ℤ) :
    symplecticPairingOmega6 v w = -symplecticPairingOmega6 w v := sorry

theorem symplecticPairingOmega6_N_invariant (v w : Fin 4 → ℤ) :
    symplecticPairingOmega6 (ModularFamilyS6.N *ᵥ v) w +
    symplecticPairingOmega6 v (ModularFamilyS6.N *ᵥ w) = 0 := sorry

theorem symplecticPairingOmega6_T0_invariant (v w : Fin 4 → ℤ) :
    symplecticPairingOmega6 (ModularFamilyS6.T0 *ᵥ v) (ModularFamilyS6.T0 *ᵥ w) =
    symplecticPairingOmega6 v w := sorry

/-! ### 4. Classical Yukawa Coupling & Mirror Map -/

def C_zzz (kappa0 mu : ℚ) (z : ℚ) : ℚ :=
  kappa0 / (z^3 * (1 - mu * z))

def Yukawa (kappa0 mu : ℚ) (z : ℚ) : ℚ :=
  C_zzz kappa0 mu z

def regularizedYukawa (kappa0 mu : ℚ) (z : ℚ) : ℚ :=
  kappa0 / (1 - mu * z)

def conifoldRegularizedYukawa (kappa0 : ℚ) (z : ℚ) : ℚ :=
  kappa0 / z^3

theorem yukawa_cusp_factorization (kappa0 mu z : ℚ) (hz : z ≠ 0) (_hcon : 1 - mu * z ≠ 0) :
    z^3 * Yukawa kappa0 mu z = regularizedYukawa kappa0 mu z := sorry

theorem regularizedYukawa_at_cusp (kappa0 mu : ℚ) :
    regularizedYukawa kappa0 mu 0 = kappa0 := sorry

theorem yukawa_conifold_factorization (kappa0 mu z : ℚ) (hz : z ≠ 0) (hcon : 1 - mu * z ≠ 0) :
    (1 - mu * z) * Yukawa kappa0 mu z = conifoldRegularizedYukawa kappa0 z := sorry

theorem conifoldRegularizedYukawa_at_conifold (kappa0 mu : ℚ) (hmu : mu ≠ 0) :
    conifoldRegularizedYukawa kappa0 (1 / mu) = kappa0 * mu^3 := sorry

theorem discriminant_root (mu z : ℚ) (hmu : mu ≠ 0) (hz : z = 1 / mu) :
    1 - mu * z = 0 := sorry

def instantonTerm (d : ℕ) (n_d : ℤ) (q : ℚ) : ℚ :=
  (d : ℚ)^3 * (n_d : ℚ) * q^d / (1 - q^d)

def C_ttt (K0 : ℚ) (n : ℕ → ℤ) (M : ℕ) (q : ℚ) : ℚ :=
  K0 + ∑ d ∈ Finset.Icc 1 M, instantonTerm d (n d) q

def instantonYukawa (K0 : ℚ) (n : ℕ → ℤ) (k : ℕ) (q : ℚ) : ℚ :=
  C_ttt K0 n k q

theorem C_ttt_zero (K0 : ℚ) (n : ℕ → ℤ) (M : ℕ) :
    C_ttt K0 n M 0 = K0 := sorry

theorem instantonYukawa_zero (K0 : ℚ) (n : ℕ → ℤ) (k : ℕ) :
    instantonYukawa K0 n k 0 = K0 := sorry

theorem instantonTerm_deg1 (n1 : ℤ) (q : ℚ) :
    instantonTerm 1 n1 q = (n1 : ℚ) * q / (1 - q) := sorry

theorem instantonTerm_deg2 (n2 : ℤ) (q : ℚ) :
    instantonTerm 2 n2 q = 8 * (n2 : ℚ) * q^2 / (1 - q^2) := sorry

theorem C_ttt_M1 (K0 : ℚ) (n : ℕ → ℤ) (q : ℚ) :
    C_ttt K0 n 1 q = K0 + (n 1 : ℚ) * q / (1 - q) := sorry

theorem instantonYukawa_k1 (K0 : ℚ) (n : ℕ → ℤ) (q : ℚ) :
    instantonYukawa K0 n 1 q = K0 + (n 1 : ℚ) * q / (1 - q) := sorry

theorem C_ttt_M2 (K0 : ℚ) (n : ℕ → ℤ) (q : ℚ) :
    C_ttt K0 n 2 q = K0 + (n 1 : ℚ) * q / (1 - q) + 8 * (n 2 : ℚ) * q^2 / (1 - q^2) := sorry

theorem instantonYukawa_k2 (K0 : ℚ) (n : ℕ → ℤ) (q : ℚ) :
    instantonYukawa K0 n 2 q = K0 + (n 1 : ℚ) * q / (1 - q) + 8 * (n 2 : ℚ) * q^2 / (1 - q^2) := sorry

def quintic_n : ℕ → ℤ
  | 1 => 2875
  | 2 => 609250
  | _ => 0

theorem quintic_instanton_k1 (q : ℚ) :
    instantonYukawa 5 quintic_n 1 q = 5 + 2875 * q / (1 - q) := sorry

theorem quintic_instanton_k2 (q : ℚ) :
    instantonYukawa 5 quintic_n 2 q = 5 + 2875 * q / (1 - q) + 4874000 * q^2 / (1 - q^2) := sorry

def modular_34_n : ℕ → ℤ
  | 1 => 4
  | 2 => -2
  | _ => 0

theorem modular_34_instanton_k1 (q : ℚ) :
    instantonYukawa 1 modular_34_n 1 q = 1 + 4 * q / (1 - q) := sorry

theorem modular_34_instanton_k2 (q : ℚ) :
    instantonYukawa 1 modular_34_n 2 q = 1 + 4 * q / (1 - q) - 16 * q^2 / (1 - q^2) := sorry

end PicardFuchsMirrorMonodromy
