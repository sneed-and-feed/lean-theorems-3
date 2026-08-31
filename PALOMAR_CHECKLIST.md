# Palomar Submission Master Priority Queue: Repo 3

All 15 theorem packages have completed pre-flight verification audits.
- **Tier-1 Verified Submission Queue**: 12 landmark research-grade packages, 100% verified (0 custom axioms, 0 `sorry`), with dedicated immutable 40-character Git commit SHAs.
- **High-Value Research Scaffolds**: 2 spectral expander packages with clearly isolated minimal axioms.
- **Retired Candidates**: 1 package crossed off early (superseded by `kelley_meka`).

### Submission Settings (`submit.palomar-registry.org`):
- **Repository**: `sneed-and-feed/lean-theorems-3`
- **Git Commit SHA**: `git rev-parse HEAD` (run `git push origin main` first)
- **Comparator Path**: `comparator.json` *(or `palomar/<slug>/comparator.json`)*
- **Existing Palomar ID**: *(leave blank)*
- **Relationship**: `Maintainer` / `Author`

---

## 🚀 Tier-1 Verified Submission Queue (100% Verified, 0 Axioms, Research-Grade)

| # | Theorem Title | Slug | Dedicated Commit SHA to Enter | Mathematical Domain |
| :---: | :--- | :--- | :--- | :--- |
| **1** | **Brieskorn Manifolds, Topological Spheres, and the 28 Exotic 7-Spheres** | `brieskorn_manifolds` | `42d3890e28ce7ec6451bb926768c125cc56f8c46` | Differential Topology / Exotic Spheres |
| **2** | **Irreducible $SU(2)$ Character Varieties of Brieskorn Homology Spheres** | `brieskorn_su2_character_variety` | `21e922a8b92c4503b8d15ce45ab23b9392abb5f0` | Gauge Theory / Casson Invariants |
| **3** | **The Kelley–Meka Theorem: Strong Bounds for 3-Progressions** | `kelley_meka` | `511b44146d7f4dfb497b225884ba0c4ea94590d1` | Additive Combinatorics / Harmonic Analysis |
| **4** | **The Discrete Cheeger Inequality for Regular Graphs** | `discrete_cheeger` | `d6eda483c45efa793e475d2f1321a525d8944794` | Spectral Graph Theory / Isoperimetry |
| **5** | **Tanner's Vertex Expansion Bound for Regular Graphs** | `tanner_expansion` | `81a4f78f6097090c4df89c6b326ac9f1c54d2c7e` | Spectral Graph Theory / Expanders |
| **6** | **Hyperbolic Orbifold Spectral Zeta & the Selberg Trace Formula** | `orbifold_spectral_zeta` | `f8c32bf5a68a2c928f2a2f2780b85a8fe244e523` | Automorphic Forms / Spectral Geometry |
| **7** | **Order-4 Picard–Fuchs Equations, Monodromy & Mirror Yukawa Couplings** | `picard_fuchs_mirror_monodromy` | `4f842837c773e6a558fe2064198b6aa23521a168` | Mirror Symmetry / Calabi–Yau |
| **8** | **Deligne–Schmid Mixed Hodge Weight Filtration $W_\bullet(N)$ & Monodromy** | `universal_monodromy_weight_filtration` | `162fa633f51d4ac29e0762cd013a7944cd653209` | Hodge Theory / Monodromy |
| **9** | **Gilmer's Entropy Bound on Frankl's Union-Closed Sets Conjecture** | `gilmer_union_closed` | `a21ba2ed4fb4de4a8220bf3f13a3eac857ca5802` | Extremal Combinatorics / Information Theory |
| **10** | **Ruzsa Distance, Plünnecke–Ruzsa Bounds & Petridis Magnification** | `ruzsa_freiman` | `e9f647dbe83af9b300ece231a240142ec21af11d` | Additive Combinatorics / Sumsets |
| **11** | **Szemerédi's Regularity Lemma and Partition Energy Dynamics** | `szemeredi_regularity` | `ca91141a2d5c5c5733723a43abf3b3e88472884b` | Extremal Graph Theory / Regularity |
| **12** | **The Cauchy–Davenport Theorem and Iterated Sumsets** | `cauchy_davenport` | `cb87e2ab9085a5d459cd70163e33755670e57b5a` | Additive Number Theory / Finite Fields |

---

## 🔬 High-Value Research Scaffolds (Explicitly Isolated Minimal Axioms)

| # | Theorem Title | Slug | Dedicated Commit SHA | Minimal Missing Prerequisites |
| :---: | :--- | :--- | :--- | :--- |
| **1** | **The Alon–Boppana Spectral Bound and Ramanujan Expanders** | `alon_boppana` | `f78939a02d8893328ee17a24a1e75d2f32edc29f` | 2 axioms: Nilli spherical Chebyshev trace on universal tree $\mathbb{T}_d$ |
| **2** | **The Expander Mixing Lemma and Spectral Discrepancy** | `expander_mixing` | `e659a70188570a755dc24f701fd4ae95ddd87ba4` | 1 axiom: Rayleigh quotient operator norm bound (provable via `tanner_expansion`) |

---

## 🛑 Retired Candidates (Did Not Meet Research Floor / Superseded)

| Slug | Core Finding & Reason for Early Retirement | Status |
| :--- | :--- | :---: |
| `roths_theorem` | **AP-18, AP-26**: Public comparator only contains 1-step iteration counting bounds ($k \alpha_0^2/16 \le 1$); full Fourier analysis unproven in submodules (superseded by `kelley_meka`). | [-] **RETIRED** |