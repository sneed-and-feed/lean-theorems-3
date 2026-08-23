import Formalization.ExpanderMixing
import Formalization.AlonBoppana
import Formalization.RuzsaFreiman
import Formalization.RothsTheorem
import Formalization.SzemerediRegularity
import Formalization.CauchyDavenport

/-!
# Lean Theorems 3: Advanced Formalization Suite

This library provides formalizations, certified proofs, and foundational scaffolds of landmark
theorems across expander graphs, spectral combinatorics, additive combinatorics, arithmetic geometry,
discrete Fourier analysis, and regularity methods in the Lean 4 / Mathlib ecosystem.

## Module Index

1. **Spectral Graph Theory & Expanders**:
   - `Formalization.ExpanderMixing`: Expander Mixing Lemma (Alon–Chung eigenvalue bound connecting edge discrepancy to $\lambda(G)$).
   - `Formalization.AlonBoppana`: Alon–Boppana Spectral Bound for $d$-regular graphs ($\lambda_2 \ge 2\sqrt{d-1} - o(1)$) and Ramanujan graphs.

2. **Additive Combinatorics & Sumset Calculus**:
   - `Formalization.RuzsaFreiman`: Complete Ruzsa calculus and Freiman structural package:
     - `Basic.lean`: Sumsets $A + B$, difference sets $A - B$, doubling constants $\sigma(A)$, and difference constants $\delta(A)$.
     - `RuzsaDistance.lean`: Ruzsa distance $d_R(A, B)$ and the Ruzsa Triangle Inequality $|B| |A - C| \le |A - B| |B - C|$.
     - `PlunneckeRuzsa.lean`: Plünnecke–Ruzsa bounds $|k B - \ell B| \le K^{k+\ell} |A|$ and Petridis minimal magnification.
     - `FreimanTheorem.lean`: Multi-dimensional Generalized Arithmetic Progressions (GAPs), Freiman's theorem in $\mathbb{Z}$, Bogolyubov's lemma, and Polynomial Freiman–Ruzsa (PFR) in $\mathbb{F}_2^n$.

3. **Arithmetic Progressions & Harmonic Analysis**:
   - `Formalization.RothsTheorem`: Complete Roth theorem scaffold:
     - `ThreeAP.lean`: Combinatorial structure of 3-term arithmetic progressions and counting functionals.
     - `FourierAnalysis.lean`: Discrete Fourier transform on finite abelian groups, Plancherel identity, and large Fourier coefficient dichotomy.
     - `DensityIncrement.lean`: Dirichlet approximation, density increment lemma ($\ge \alpha + \alpha^2 / 16$), and quantitative $r_3(N)$ bounds (Roth, Kelley–Meka).

4. **Extremal Graph Theory & Regularity**:
   - `Formalization.SzemerediRegularity`: Complete Szemerédi regularity package:
     - `PairDensity.lean`: Pair edge density $d(X, Y)$ and $\varepsilon$-regular pairs.
     - `EnergyIncrement.lean`: Mean-square partition energy $E(\mathcal{P})$, Cauchy–Schwarz monotonicity, and the Energy Increment Lemma ($+\varepsilon^5/2$).
     - `RegularityLemma.lean`: Szemerédi's Regularity Lemma, Triangle Counting Lemma, Triangle Removal Lemma, and graph-theoretic deduction of Roth's theorem.

5. **Additive Number Theory & Finite Fields**:
   - `Formalization.CauchyDavenport`: Cauchy–Davenport theorem over $\mathbb{Z}/p\mathbb{Z}$, Davenport's e-transform, Vosper's critical pairs theorem, Chowla's composite generalization, and Erdős–Ginzburg–Ziv theorem.
-/
