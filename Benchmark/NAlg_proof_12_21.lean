import Mathlib

set_option linter.style.longLine false

open Matrix WithLp



namespace NAlg_P12

def diagonalizable {n : Type u} [Fintype n] [DecidableEq n] {R : Type v} [CommRing R]
    (A : Matrix n n R) : Prop :=
  ∃ (P : Matrix n n R) (D : Matrix n n R), IsUnit P ∧ IsDiag D ∧ A = P⁻¹ * D * P

/--
P8.7.4 Show that if $C$ is real and diagonalizable, then there exist symmetric matrices $A$ and $B, B$ nonsingular, such that $C=A B^{-1}$. This shows that symmetric pencils $A-\lambda B$ are essentially general.
-/
theorem exists_symmetric_factorization_of_diagonalizable_real_matrix {n : ℕ} [NeZero n] :
    ∀ (C : Matrix (Fin n) (Fin n) ℝ), diagonalizable C →
    ∃ (A B : Matrix (Fin n) (Fin n) ℝ), Aᵀ = A ∧ Bᵀ = B ∧ IsUnit B ∧ C = A * B⁻¹ := by
  sorry

end NAlg_P12



namespace NAlg_P13

/--
`singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᵀ * A`.
-/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℝ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℝ := Aᵀ * A
  have hSymm : IsSymm M := by
    rw [Matrix.IsSymm, transpose_mul, transpose_transpose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hSymm
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def maximum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  singularValues A ⟨0, n.pos_of_neZero⟩

/--
P2.4.2 Prove that if $A \in \mathbb{R}^{m \times n}$, then

$$
\sigma_{\max}(A) = \max_{\substack{y \in \mathbb{R}^m \\ x \in \mathbb{R}^n}} \frac{y^T A x}{\|x\|_2\|y\|_2}
$$
-/
theorem maximum_singular_value_eq_sup_ratio {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) : maximum_singular_value A =
    ⨆ (x : Fin n → ℝ) (y : Fin m → ℝ) (hx : x ≠ 0) (hy : y ≠ 0),
      (y ⬝ᵥ A *ᵥ x) / (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) := by
  sorry

end NAlg_P13



namespace NAlg_P14

/--
`singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᵀ * A`.
-/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℝ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℝ := Aᵀ * A
  have hSymm : IsSymm M := by
    rw [Matrix.IsSymm, transpose_mul, transpose_transpose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hSymm
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
P6.2.7 Suppose

$$
A=\left[\begin{array}{l}
A_1 \\
A_2
\end{array}\right]
$$

where $A_1 \in \mathbb{R}^{n \times n}$ is nonsingular and $A_2 \in \mathbb{R}^{(m-n) \times n}$. Show that

$$
\sigma_{\min }(A) \geq \sqrt{1+\sigma_{\min }\left(A_2 A_1^{-1}\right)^2} \quad \sigma_{\min }\left(A_1\right) .
$$ All the matrix are real matrix
-/
theorem minimum_singular_value_fromRows_lower_bound {m n : ℕ} [NeZero m] [NeZero n] (hn : n < m)
    (A₁ : Matrix (Fin n) (Fin n) ℝ) (A₂ : Matrix (Fin (m - n)) (Fin n) ℝ)
    (hA₁ : IsUnit A₁) (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A = fun i j ↦ fromRows A₁ A₂
      ((Finite.equivFinOfCardEq (by simp; omega)).symm i) j) :
    haveI : NeZero (m - n) := { out := Nat.sub_ne_zero_iff_lt.mpr hn}
    minimum_singular_value A ≥
    Real.sqrt (1 + (minimum_singular_value (A₂ * A₁⁻¹)) ^ 2) * minimum_singular_value A₁ := by
  sorry

end NAlg_P14



namespace NAlg_P15

/--
P9.4.8 Show that the polar decomposition of a nonsingular matrix is unique. Hint: If $A=U_1 P_1$ and $A=U_2 P_2$ are two polar decompositions, then $U_2^T U_1=P_2 P_1^{-1}$ and $U_1^T U_2=P_1 P_2^{-1}$ have the same eigenvalues. All the matrix are real matrix
-/
theorem polar_decomposition_unique {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    [Invertible A] (U1 U2 P1 P2 : Matrix n n ℝ)
    (hU1 : U1 ∈ orthogonalGroup n ℝ) (hU2 : U2 ∈ orthogonalGroup n ℝ)
    (hP1 : PosDef P1) (hP2 : PosDef P2) (h1 : A = U1 * P1) (h2 : A = U2 * P2) :
    U1 = U2 ∧ P1 = P2 := by
  sorry

end NAlg_P15



namespace NAlg_P16

variable {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : IsSymm A)

/-- Rayleigh quotient `r(x) = (xᵀ A x)/(xᵀ x)` for a real symmetric matrix. -/
noncomputable def rayleighQuotient (x : EuclideanSpace ℝ n) : ℝ :=
  (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)

/--
P10.1.2 Let $A \in \mathbb{R}^{n \times n}$ be symmetric and define $r(x)=x^T A x / x^T x$.

Suppose $S \subseteq \mathbb{R}^n$ isa subspace with the property that $x \in S$ implies $\nabla r(x) \in S$.

Show that $S$ is invariant for $A$.
-/
theorem rayleigh_quotient_gradient_in_submodule (S : Submodule ℝ (EuclideanSpace ℝ n))
    (hgrad : ∀ x ∈ S, gradient (fun y ↦ rayleighQuotient A y) x ∈ S) :
    ∀ x ∈ S, (A *ᵥ x) ∈ (EuclideanSpace.equiv n ℝ) '' S := by
  sorry

end NAlg_P16



namespace NAlg_P17

-- Note : #check Matrix.det_of_upperTriangular
-- #check Matrix.det_of_lowerTriangular gives some examples of how to describe L and U in mathlib

/-- Theorem 4.2.6. Let $A \in \mathbb{R}^{n \times n}$ be positive definite and set $T=\left(A+A^T\right) / 2$ and $S=\left(A-A^T\right) / 2$. If $A=LU$ is the LU factorization, then

$$
\left\| |L| \cdot | U| \right\|_F \leq n\left(\|T\|_2+\|S T^{-1} S\|_2\right)
$$
-/
theorem frobenius_norm_LU_bound {n : ℕ} [NeZero n] (A L U T S : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.PosDef A) (HL1 : ∀ i, L.diag i = 1) (hL : L.BlockTriangular OrderDual.toDual)
    (hU : U.BlockTriangular id) (hLU : A = L * U) (hT : T = (A + Aᵀ) / 2) (hS : S = (A - Aᵀ) / 2) :
    frobeniusSeminormedAddCommGroup.norm (abs.comp L * abs.comp U) ≤
    n * (instL2OpNormedAddCommGroup.norm T + instL2OpNormedAddCommGroup.norm (S * T⁻¹ * S)) := by
  sorry

end NAlg_P17



namespace NAlg_P18

/--
P6.2.4 (a) Show that if $\left(A^T A+\lambda I\right) x=A^T b, \lambda>0$,

and $\|x\|_2=\alpha$, then $z=(A x-b) / \lambda$ solves the dual equations

$\left(A A^T+\lambda I\right) z=-b$ with $\left\|A^T z\right\|_2=\alpha$.
-/
theorem regularized_lstsq_primal_to_dual {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (lam : ℝ) (x : Fin n → ℝ) (α : ℝ)
    (hlam : lam > 0) (h1 : (Aᵀ * A + lam • 1) *ᵥ x = Aᵀ *ᵥ b) (h2 : ‖x‖ = α) (z : Fin m → ℝ)
    (hz : z = lam⁻¹ • (A *ᵥ x - b)) : (A * Aᵀ + lam • 1) *ᵥ z = -b ∧ ‖Aᵀ *ᵥ z‖ = α := by
  sorry

/--
(b) Show that if $\left(A A^T+\lambda I\right) z=-b$,

$\left\|A^T z\right\|_2=\alpha$, then $x=-A^T z$ satisfies $\left(A^T A+\lambda I\right) x=A^T b,\|x\|_2=\alpha$.
-/
theorem regularized_lstsq_dual_to_primal {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (lam : ℝ) (z : Fin m → ℝ) (α : ℝ)
    (hlam : lam > 0) (h1 : (A * Aᵀ + lam • 1) *ᵥ z = -b) (h2 : ‖Aᵀ *ᵥ z‖ = α) (x : Fin n → ℝ)
    (hx : x = -Aᵀ *ᵥ z) : (Aᵀ * A + lam • 1) *ᵥ x = Aᵀ *ᵥ b ∧ ‖x‖ = α := by
  sorry

end NAlg_P18



namespace NAlg_P19

/--
P6.2.3 Suppose $Y=\left[y_1|\cdots| y_k\right] \in \mathbb{R}^{m \times k}$ has the property that

$$
Y^T Y=\operatorname{diag}\left(d_1^2, \ldots, d_k^2\right), \quad d_1 \geq d_2 \geq \cdots \geq d_k>0
$$

Show that if $Y=Q R$ is the QR factorization of $Y$, then $R$ is diagonal with $\left|r_{i i}\right|=d_i$. All the matrix are real matrix
-/
theorem QR_diagonal_from_orthogonal_columns {m k : ℕ} [NeZero m] [NeZero k]
    (Y : Matrix (Fin m) (Fin k) ℝ) (hle : m ≥ k) (d : Fin k → ℝ) (h_diag_pos : ∀ i, d i > 0)
    (h_diag_noninc : ∀ i j, i ≤ j → d i ≥ d j)
    (h_YTY_diag : Yᵀ * Y = diagonal (fun i ↦ (d i) ^ 2))
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin k) ℝ) (hQR : Y = Q * R)
    (hQ : Q ∈ orthogonalGroup (Fin m) ℝ)
    (h_R : ∀ (i : Fin m) (j : Fin k), (j : ℕ) < i → R i j = 0) :
    R = of fun (i : Fin m) (j : Fin k) => if (i : ℕ) = j then d j else 0 := by
  sorry

end NAlg_P19



namespace NAlg_P20

/--
`singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᵀ * A`.
-/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℝ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℝ := Aᵀ * A
  have hSymm : IsSymm M := by
    rw [Matrix.IsSymm, transpose_mul, transpose_transpose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hSymm
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
P6.5.2 Suppose

$$
A=\left[\begin{array}{c}
c^T \\
B
\end{array}\right], \quad c \in \mathbb{R}^n, B \in \mathbb{R}^{(m-1) \times n}
$$

has full column rank and $m>n$. Using the Sherman-Morrison-Woodbury formula show that

$$
\frac{1}{\sigma_{\min }(B)} \leq \frac{1}{\sigma_{\min }(A)}+\frac{\left\|\left(A^T A\right)^{-1} c\right\|_2^2}{1-c^T\left(A^T A\right)^{-1} c}
$$ All the matrix are real matrix
-/
theorem minimum_singular_value_bound_for_augmented_matrix {m n : ℕ} [NeZero m] [NeZero n]
    (h : m > n) (c : Fin n → ℝ) (B : Matrix (Fin (m - 1)) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (fullRank : rank A = n)
    (hA : A = of (fun (i : Fin m) j => if h : (i : ℕ) = 0 then c j
      else B ⟨(i : ℕ) - 1, by omega⟩ j)) :
    haveI : NeZero (m - 1) :=
      have : n > 0 := n.pos_of_neZero
      NeZero.of_pos (by omega)
    IsUnit (Aᵀ * A) ∧ IsUnit (Bᵀ * B) ∧
    1 / minimum_singular_value B ≤ 1 / minimum_singular_value A +
      ‖(Aᵀ * A)⁻¹ *ᵥ c‖ ^ 2 / (1 - (c ⬝ᵥ (Aᵀ * A)⁻¹ *ᵥ c)) := by
  sorry

end NAlg_P20



namespace NAlg_P21

open scoped Matrix.Norms.Operator

variable {n : ℕ} [NeZero n] {A L U : Matrix (Fin n) (Fin n) ℝ}

/--
P3.4.1 Let $A=L U$ be the LU factorization of $n$-by-$n A$ with $\left|\ell_{i j}\right| \leq 1$.

Let $a_i^T$ and $u_i^T$ denotethe $i$ th rows of $A$ and $U$, respectively. Verify the equation

$$
u_i^T=a_i^T-\sum_{j=1}^{i-1} \ell_{i j} u_j^T
$$

and use it to show that $\|U\|_{\infty} \leq 2^{n-1}\|A\|_{\infty}$. (Hint: Take norms and use induction.)
-/
theorem LU_factorization_prop (hL1 : ∀ i, L.diag i = 1) (hL : L.BlockTriangular OrderDual.toDual)
    (hU : U.BlockTriangular id) (hLU : A = L * U) (i : Fin n) :
    U i = A i - ∑ j ∈ Finset.filter (fun j => j < i) Finset.univ, L i j • U j := by
  sorry

theorem LU_factorization_norm_bound (hL1 : ∀ i, L.diag i = 1)
    (hL : L.BlockTriangular OrderDual.toDual) (hU : U.BlockTriangular id) (hLU : A = L * U)
    (i : Fin n) : ‖U‖ ≤ (2 : ℝ) ^ (n - 1) * ‖A‖ := by
  sorry

end NAlg_P21
