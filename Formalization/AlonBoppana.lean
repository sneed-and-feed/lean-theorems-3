import Formalization.AlonBoppana.Basic
import Formalization.AlonBoppana.SphericalShell
import Formalization.AlonBoppana.NilliProfile
import Formalization.AlonBoppana.SpectralBound

open scoped BigOperators Matrix Finset
open Classical

set_option linter.unusedSectionVars false

/-!
# The Alon–Boppana Spectral Lower Bound for Regular Graphs

This module formalizes the **Alon–Boppana Theorem** (Noga Alon and Ravi Boppana, 1986; Alon Nilli, 1991)
on the fundamental lower bound on the second largest eigenvalue of $d$-regular graphs.

## Mathematical Overview

Let $G = (V, E)$ be a finite, connected, $d$-regular simple graph on $n$ vertices with diameter $D = \mathrm{diam}(G)$.
Let $A \in M_{V \times V}(\mathbb{R})$ be its adjacency matrix:
$$A(u, v) = \begin{cases} 1 & \text{if } u \sim v \\ 0 & \text{otherwise} \end{cases}$$

Since $G$ is $d$-regular and connected:
1. The largest eigenvalue of $A$ is $\lambda_1(A) = d$.
2. The constant vector $\mathbf{1} = (1, 1, \dots, 1)^T$ is an eigenvector: $A \mathbf{1} = d \mathbf{1}$.
3. The **second largest eigenvalue** $\lambda_2(G) = \lambda_2(A)$ is given by the Courant–Fischer variational min-max theorem:
   $$\lambda_2(A) = \max_{\substack{v \in \mathbb{R}^V \setminus \{0\} \\ v \perp \mathbf{1}}} \frac{\langle v, A v \rangle}{\langle v, v \rangle}$$

### The Alon–Boppana Lower Bound

Alon and Boppana established that graph geometry (specifically diameter and degree) imposes an unavoidable
lower bound on $\lambda_2(G)$:
$$\lambda_2(A) \ge 2\sqrt{d-1} \cdot \left(1 - \frac{2}{D}\right) - \frac{O(1)}{D}$$

In 1991, Alon Nilli provided an elegant, purely combinatorial proof using localized spherical shell test functions
$f(x) = (d-1)^{-k/2}$ on $S_k(x_0)$, showing:
$$\lambda_2(G) \ge 2\sqrt{d - 1} - \frac{2\sqrt{d - 1} - 1}{\lfloor D / 2 \rfloor}$$

### Asymptotic Consequence & Ramanujan Graphs

For any sequence of $d$-regular graphs $\{G_n\}$ with $|V(G_n)| \to \infty$ (implying $D(G_n) \to \infty$ by Moore's bound):
$$\liminf_{n \to \infty} \lambda_2(G_n) \ge 2\sqrt{d-1}$$

A $d$-regular graph is called a **Ramanujan graph** (Lubotzky–Phillips–Sarnak 1988, Margulis 1988) if
every non-trivial eigenvalue $\lambda \ne \pm d$ satisfies the optimal bound:
$$|\lambda| \le 2\sqrt{d-1}$$
Thus, Ramanujan graphs are optimal expanders achieving the maximal spectral gap $d - 2\sqrt{d-1}$.

## Formalization Architecture

The formalization is structured into four modular, golfed submodules:
1. `Formalization.AlonBoppana.Basic`:
   - `adjacencyMatrix`: 0-1 real adjacency matrix.
   - `isRegularOfDegree`: $d$-regularity predicate.
   - `innerProduct`, `normSq`, `rayleighQuotient`: Euclidean inner product, squared norm, and Rayleigh quotient.
   - `isOrthogonalToOnes`: Orthogonality to $\mathbf{1}$.
   - `adjacencyMatrix_symmetric`, `adjacencyMatrix_mul_ones`, `normSq_pos_of_ne_zero`.
2. `Formalization.AlonBoppana.SphericalShell`:
   - `sphericalShell`: Finset of vertices at distance $k$ from a base vertex $x_0$.
   - `sphericalShell_disjoint`, `sphericalShell_zero`, `sphericalShell_one`.
   - `backwardNeighbors`, `internalNeighbors`, `forwardNeighbors`: Neighbor degree partition.
   - `card_backwardNeighbors_ge_one`, `forwardNeighbors_card_le_d_sub_one`.
3. `Formalization.AlonBoppana.NilliProfile`:
   - `nilliProfile`: Geometric radial weight profile $g(k) = (d-1)^{-k/2}$.
   - `nilliProfile_mul_succ`: Step product identity $g(k)g(k+1) = \sqrt{d-1} g(k+1)^2$.
   - `radialTestVector`, `nilliTestVector`: Spherical shell test vectors.
   - `orthogonalLinearCombination`: Balanced orthogonal combination $f = (\sum f_2) f_1 - (\sum f_1) f_2$.
   - `rayleighQuotient_orthogonalCombination`: Variational ratio bound $\min(R(f_1), R(f_2)) \le R(f)$.
   - `nilliSignedTestVector_ne_zero`: Non-triviality under separation $2r+1 \le \mathrm{dist}(x_0, y_0)$.
4. `Formalization.AlonBoppana.SpectralBound`:
   - `secondEigenvalue`: Variational second eigenvalue $\lambda_2(G)$.
   - `alon_boppana_bound`: Non-asymptotic lower bound $\lambda_2 \ge 2\sqrt{d-1}(1 - 2/D) - 2/D$.
   - `alon_boppana_nilli`: Nilli's diameter-based bound $\lambda_2 \ge 2\sqrt{d-1} - (2\sqrt{d-1}-1)/\lfloor D/2 \rfloor$.
   - `IsRamanujan`: Ramanujan graph predicate.
   - `ramanujan_spectral_gap`: Verified spectral gap $d - \lambda_2 \ge d - 2\sqrt{d-1}$.

## References

- Alon, N. (1986). *Eigenvalues and expanders*. Theory of Computing Systems, 19(1), 283–296.
- Nilli, A. (1991). *On the second eigenvalue of a graph*. Discrete Mathematics, 91(2), 207–210.
- Lubotzky, A., Phillips, R., & Sarnak, P. (1988). *Ramanujan graphs*. Combinatorica, 8(3), 261–277.
- Marcus, A. W., Spielman, D. A., & Srivastava, N. (2015). *Interlacing families I: Bipartite Ramanujan graphs of all degrees*. Annals of Mathematics, 182(1), 307–325.
-/
