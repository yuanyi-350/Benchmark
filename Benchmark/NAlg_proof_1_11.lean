import Mathlib

set_option linter.style.longLine false

open Matrix WithLp



namespace NAlg_P1

/--
P2.1.1 Show that if $A \in \mathbb{R}^{m \times n}$ has rank $p$, then there exists an $X \in \mathbb{R}^{m \times p}$ and a $Y \in \mathbb{R}^{n \times p}$ such that $A=X Y^T$, where $\operatorname{rank}(X)=\operatorname{rank}(Y)=p$.
-/
theorem rank_factorization {m n p : ℕ} [NeZero m] [NeZero n] [NeZero p]
    (A : Matrix (Fin m) (Fin n) ℝ) (h : rank A = p) :
    ∃ (X : Matrix (Fin m) (Fin p) ℝ) (Y : Matrix (Fin n) (Fin p) ℝ),
      A = X * Yᵀ ∧ rank X = p ∧ rank Y = p := by
  sorry

end NAlg_P1



namespace NAlg_P2

variable {n : ℕ} [NeZero n]

/--
P2.1.9 Show that if $S$ is real and $S^T=-S$, then $I-S$ is nonsingular and the matrix $(I-S)^{-1}(I+S)$ is orthogonal.
-/
theorem isUnit_one_sub_skew_symmetric (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) :
    IsUnit (1 - S) := by
  sorry

theorem cayley_transform_orthogonal (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) : (1 - S)⁻¹ * (1 + S) ∈ orthogonalGroup (Fin n) ℝ := by
  sorry

end NAlg_P2



namespace NAlg_P3

/--
P5.1.2 Show that $\operatorname{det}\left(I+x y^T\right)=1+x^T y$ where $x$ and $y$ are given $m$-vectors.
-/
theorem det_identity_plus_outer_product {m : ℕ} [NeZero m] (x y : Fin m → ℝ) :
    det (1 + vecMulVec x y) = 1 + x ⬝ᵥ y := by
  sorry

end NAlg_P3



namespace NAlg_P4

/--
P5.5.8 Suppose $A \in \mathbb{R}^{m \times n}$ and that $\left\|u^T A\right\|_2 = \sigma$ with $u^T u=1$.

Show that if $u^T(A x-b)=0$ for $x \in \mathbb{R}^n$ and $b \in \mathbb{R}^m$, then $\|x\|_2 \geq\left|u^T b\right| / \sigma$.
-/
theorem least_squares_residual_lower_bound {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℝ) (u b : Fin m → ℝ) (x : Fin n → ℝ) (σ : ℝ)
    (h_norm_u : ‖toLp 2 u‖ = 1)
    (h_norm_utA : ‖toLp 2 u ᵥ* A‖ = σ) (h_ortho : u ⬝ᵥ (A *ᵥ x - b) = 0) :
    ‖toLp 2 x‖ ≥ |u ⬝ᵥ b| / σ := by
  sorry

end NAlg_P4



namespace NAlg_P5

/--
P5.2.12 Show that if $A \in \mathbb{R}^{n \times n}$ and $a_i=A(:, i)$, then

$$
|\operatorname{det}(A)| \leq\left\|a_1\right\|_2 \cdots\left\|a_n\right\|_2 .
$$
-/
theorem abs_det_le_product_norm_columns {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i : Fin n, ‖toLp 2 (Aᵀ i)‖ := by
  sorry

end NAlg_P5



namespace NAlg_P6

/--
Lemma 5.1.1. Suppose $Q=I_m-W Y^T$ is an $m$-by-$m$ orthogonal matrix with $W, Y \in \mathbb{R}^{m \times j}$.

If $P=I_m-\beta v v^T$ with $v \in \mathbb{R}^m$ and $z=\beta Q v$, then

$$
Q_{+} = Q P = I_m - W_{+} Y_{+}^T
$$

where $W_{+}=[W \mid z]$ and $Y_{+}=[Y \mid v]$ are each $m$-by-$(j+1)$.
-/
theorem orthogonal_update_identity {m j : ℕ} [NeZero m] [NeZero j] (β : ℝ)
    (W Y : Matrix (Fin m) (Fin j) ℝ) (Q P : Matrix (Fin m) (Fin m) ℝ) (hQ : Q = 1 - W * Yᵀ)
    (hQ_ortho : Q ∈ orthogonalGroup (Fin m) ℝ)
    (v z : Matrix (Fin m) (Fin 1) ℝ) (hP : P = 1 - β • v * vᵀ) (hz : z = β • Q * v) :
    Q * P = 1 - (fromCols W z) * (fromCols Y v)ᵀ := by
  sorry

end NAlg_P6



namespace NAlg_P7

/--
P7.5.1 Show that if $\bar{H}=Q^T H Q$ is obtained by performing a single-shift QR step with

$$
H=\left[\begin{array}{ll}
w & x \\
y & z
\end{array}\right],
$$

then $\left|\bar{h}_{21}\right| \leq\left|y^2 x\right| /\left[(w-z)^2+y^2\right]$.
-/
theorem single_shift_QR_inequality {x y z w : ℝ} (H H_bar Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H = !![w, x; y, z]) (hQ_ortho : Q ∈ orthogonalGroup (Fin 2) ℝ)
    (h_transform : H_bar = Qᵀ * H * Q) :
    |H_bar 1 0| ≤ |y ^ 2 * x| / ((w - z) ^ 2 + y ^ 2) := by
  sorry

end NAlg_P7



namespace NAlg_P8

/--
Theorem 4.2.3. The matrix $A \in \mathbb{R}^{n \times n}$ is positive definite if and only if the symmetric matrix

$$
T=\frac{A+A^T}{2}
$$

has positive eigenvalues.
-/
theorem posdef_iff_symmetric_eigenvalues_positive {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsSymm A) :
    PosDef A ↔ ∀ μ, Module.End.HasEigenvalue (toLin' ((1/2 : ℝ) • (A + Aᵀ))) μ → 0 < μ := by
sorry

end NAlg_P8



namespace NAlg_P9

/--
Section 4.4.5. A very important class of symmetric indefinite matrices have the form

$$
A=\left[\begin{array}{cc}
C & B \\
B^T & 0
\end{array}\right]_p^n
$$

where $C$ is symmetric positive definite and $B$ has full column rank. Show that $A$ is nonsingular. All the matrix are real matrix
-/
theorem symmetric_indefinite_nonsingular {p n : ℕ} [NeZero p] [NeZero n]
    (C : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin n) ℝ) (hC_posdef : PosDef C)
    (hB_rank : rank B = n) : IsUnit (fromBlocks C B (Bᵀ) 0) := by
  sorry

end NAlg_P9



namespace NAlg_P10

/--
P6.2.4 (b) Show that if $\left(A A^T+\lambda I\right) z=-b$, $\left\|A^T z\right\|_2=\alpha$,

then $x=-A^T z$ satisfies $\left(A^T A+\lambda I\right) x=A^T b,\|x\|_2=\alpha$.
-/
theorem problem_6_2_4_b {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℝ) (l α : ℝ)
    (b z : Fin m → ℝ) (h1 : (A * Aᵀ + l • 1) *ᵥ z = -b) (h2 : ‖toLp 2 (Aᵀ *ᵥ z)‖ = α)
    (x : Fin n → ℝ) (hx : x = -(Aᵀ *ᵥ z)) :
    (Aᵀ * A + l • 1) *ᵥ x = Aᵀ *ᵥ b ∧ ‖toLp 2 x‖ = α := by
  sorry

end NAlg_P10



namespace NAlg_P11

attribute [local instance] frobeniusSeminormedAddCommGroup

-- example {p : ℕ} (P : Matrix (Fin p) (Fin p) ℝ) :
--   ‖P‖ = (∑ i, ∑ j, ‖P i j‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := frobenius_norm_def P

variable {m p : ℕ} [NeZero m] [NeZero p]

/--
`singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᵀ * A`.
-/
noncomputable def singularValues (A : Matrix (Fin m) (Fin p) ℝ) : Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℝ := Aᵀ * A
  have hSymm : IsSymm M := by
    rw [Matrix.IsSymm, transpose_mul, transpose_transpose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hSymm
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

/--
P6.4.1 Show that if $A$ and $B$ are $m$-by- $p$ matrices, with $p \leq m$, then

$$
\min _{Q^T Q=I_p}\|A-B Q\|_F^2
= \sum_{i=1}^p\left(\sigma_i(A)^2 - 2 \sigma_i\left(B^T A\right) + \sigma_i(B)^2\right) .
$$
-/
theorem exercise_p6_4_1 (A B : Matrix (Fin m) (Fin p) ℝ) (hp : p ≤ m) :
    sInf {x : ℝ | ∃ Q ∈ orthogonalGroup (Fin p) ℝ,  x = ‖A - B * Q‖ ^ 2} =
    ∑ i : Fin p, ((singularValues A i) ^ 2 - 2 * singularValues (Bᵀ * A) i
    + (singularValues B i) ^ 2) := by
  sorry

end NAlg_P11
