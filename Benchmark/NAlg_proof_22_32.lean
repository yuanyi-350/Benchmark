import Mathlib

set_option linter.style.longLine false

open Matrix WithLp Pointwise



namespace NAlg_P22

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
The minimum singular value of a complex matrix $A$ is the infimum of $\|A v\|_2$ over all unit
vectors $v$ (for the $L^2$-norm)
-/

lemma minimum_singular_value_prop  {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) :
    minimum_singular_value A =
    sInf { y | ∃ v : Fin n → ℂ , ‖toLp 2 v‖ = 1 ∧ y = ‖toLp 2 (A *ᵥ v)‖} := by
  sorry

end NAlg_P22



namespace NAlg_P23

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
ε–pseudospectrum of a complex matrix A : Λ_ε(A) = { z ∈ ℂ | σ_min(A - zI) ≤ ε }
-/
noncomputable def pseudospectrum {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    Set ℂ := { z : ℂ | minimum_singular_value (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ ε }

attribute [instance] instL2OpNormedAddCommGroup

/-- Condition number with respect to the operator 2-norm. -/
noncomputable def kappa2 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖X‖ * ‖X⁻¹‖

/--
Theorem 7.9.2. If $B=X^{-1} A X$, then $\Lambda_\epsilon(B) \subseteq \Lambda_{\epsilon \kappa_2(X)}(A)$.
-/
theorem pseudospectrum_similarity_bound {n : ℕ} [NeZero n]
    (A X : Matrix (Fin n) (Fin n) ℂ) [Invertible X] (ε : ℝ) (hε : ε > 0) :
    pseudospectrum (X⁻¹ * A * X) ε ⊆ pseudospectrum A (ε * kappa2 X) := by
  sorry

end NAlg_P23



namespace NAlg_P24

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
ε–pseudospectrum of a complex matrix A : Λ_ε(A) = { z ∈ ℂ | σ_min(A - zI) ≤ ε }
-/
noncomputable def pseudospectrum {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    Set ℂ := { z : ℂ | minimum_singular_value (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ ε }

/--
Corollary 7.9.3. If $X \in \mathbb{C}^{n \times n}$ is unitary and $A \in \mathbb{C}^{n \times n}$,

then $\Lambda_\epsilon\left(X^{-1} A X\right)=\Lambda_\epsilon(A)$.
-/
theorem pseudospectrum_unitary_conjugation {n : ℕ} [NeZero n] (A X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ unitaryGroup (Fin n) ℂ) (ε : ℝ) (hε : ε > 0) :
    pseudospectrum (X⁻¹ * A * X) ε = pseudospectrum A ε  :=
  sorry

end NAlg_P24



namespace NAlg_P25

attribute [instance] instL2OpNormedAddCommGroup

/--
Theorem 8.1.13. Suppose $A \in \mathbb{R}^{n \times n}$ and $S \in \mathbb{R}^{r \times r}$ are symmetric and that

$$
A Q_1-Q_1 S=E_1
$$

where $Q_1 \in \mathbb{R}^{n \times r}$ satisfies $Q_1^T Q_1=I_r$. Then there exist $\mu_1, \ldots, \mu_r \in \lambda(A)$ such that

$$
\left|\mu_k-\lambda_k(S)\right| \leq \sqrt{2}\left\|E_1\right\|_2
$$

for $k=1: r$.
-/
theorem symmetric_eigenvalue_perturbation {n r : ℕ} [NeZero n] [NeZero r]
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (hA : IsSymm A) (hS : IsSymm S)
    (Q₁ E₁ : Matrix (Fin n) (Fin r) ℝ) (hQ₁ : Q₁ᵀ * Q₁ = 1) : ∃ μ : Fin r → spectrum ℝ A,
    ∀ (k : Fin r), |(μ k : ℝ) - LinearMap.IsSymmetric.eigenvalues
    (isHermitian_iff_isSymmetric.mp hS) (n := r) (by simp) k| ≤ Real.sqrt 2 * ‖E₁‖ := by
  sorry

end NAlg_P25



namespace NAlg_P26

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
ε–pseudospectrum of a complex matrix A : Λ_ε(A) = { z ∈ ℂ | σ_min(A - zI) ≤ ε }
-/
noncomputable def pseudospectrum {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    Set ℂ := { z : ℂ | minimum_singular_value (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ ε }


/--
Theorem 7.9.6. If

$$
T=\left[\begin{array}{cc}
T_{11} & T_{12} \\
0 & T_{22}
\end{array}\right]
$$

with square diagonal blocks, then $\Lambda_\epsilon\left(T_{11}\right) \cup \Lambda_\epsilon\left(T_{22}\right) \subseteq \Lambda_\epsilon(T)$.
-/
theorem pseudospectrum_block_triangular_inclusion {n m : ℕ} [NeZero n] [NeZero m]
    {ε : ℝ} (hε : ε > 0) (T11 : Matrix (Fin n) (Fin n) ℝ) (T12 : Matrix (Fin n) (Fin m) ℝ)
    (T22 : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) :
    haveI equiv: Fin (m + n) ≃ Fin n ⊕ Fin m :=
      (Finite.equivFinOfCardEq (by simp; omega)).symm
    (pseudospectrum (T11.map (algebraMap ℝ ℂ)) ε) ∪ (pseudospectrum (T22.map (algebraMap ℝ ℂ)) ε) ⊆
      pseudospectrum (fun i j ↦ (fromBlocks T11 T12 0 T22).map (algebraMap ℝ ℂ)
      (equiv i) (equiv j)) ε := by
  sorry

end NAlg_P26



namespace NAlg_P27

/--
P4.2.12 Show that if

$$
M=\left[\begin{array}{cc}
A & B \\
B^T & C
\end{array}\right]
$$

is symmetric positive definite and $A$ and $C$ are square, then

$$
M^{-1}=\left[\begin{array}{cc}
A^{-1}+A^{-1} B S^{-1} B^T A^{-1} & -A^{-1} B S^{-1} \\
S^{-1} B^T A^{-1} & S^{-1}
\end{array}\right], \quad S=C-B^T A^{-1} B .
$$
-/
theorem schur_complement_inverse_formula {l m : Type*} [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]
    (A : Matrix l l ℝ) (B : Matrix l m ℝ) (C : Matrix m m ℝ)
    (M : Matrix (l ⊕ m) (l ⊕ m) ℝ) (hM : M = fromBlocks A B Bᵀ C) (hPosDef : PosDef M)
    (S : Matrix m m ℝ) (hS : S = C - Bᵀ * A⁻¹ * B) :
    M⁻¹ = fromBlocks (A⁻¹ + A⁻¹ * B * S⁻¹ * Bᵀ * A⁻¹) (- A⁻¹ * B * S⁻¹)
                     (- S⁻¹ * Bᵀ * A⁻¹) (S⁻¹) := by
  sorry

end NAlg_P27



namespace NAlg_P28

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
ε–pseudospectrum of a complex matrix A : Λ_ε(A) = { z ∈ ℂ | σ_min(A - zI) ≤ ε }
-/
noncomputable def pseudospectrum {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    Set ℂ := { z : ℂ | minimum_singular_value (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ ε }

/--
Theorem 7.9.4. If $D=\operatorname{diag}\left(\lambda_1, \ldots, \lambda_n\right)$, then $\Lambda_\epsilon(D)=\left\{\lambda_1, \ldots, \lambda_n\right\}+\Delta_\epsilon$.
-/
theorem pseudospectrum_diagonal_eq_spectrum_plus_ball {n : ℕ} [NeZero n] (v : Fin n → ℂ) (ε : ℝ)
    (hε : ε > 0) :
    pseudospectrum (diagonal v) ε = (Set.range fun i ↦ v i) + Metric.closedBall (0 : ℂ) ε := by
  sorry

end NAlg_P28



namespace NAlg_P29

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
ε–pseudospectrum of a complex matrix A : Λ_ε(A) = { z ∈ ℂ | σ_min(A - zI) ≤ ε }
-/
noncomputable def pseudospectrum {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    Set ℂ := { z : ℂ | minimum_singular_value (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ ε }

/--
Corollary 7.9.5. If $A \in \mathbb{C}^{n \times n}$ is normal, then $\Lambda_\epsilon(A)=\Lambda(A)+\Delta_\epsilon$. All the matrix are real matrix
-/
theorem pseudospectrum_normal_eq_spectrum_plus_ball {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ)  (hA : A * Aᴴ = Aᴴ * A) (ε : ℝ) (hε : 0 < ε) :
    pseudospectrum A ε = spectrum ℂ A + Metric.closedBall (0 : ℂ) ε := by
  sorry

end NAlg_P29



namespace NAlg_P30

attribute [instance] instL2OpNormedAddCommGroup

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
ε–pseudospectrum of a complex matrix A : Λ_ε(A) = { z ∈ ℂ | σ_min(A - zI) ≤ ε }
-/
noncomputable def pseudospectrum {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    Set ℂ := { z : ℂ | minimum_singular_value (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ ε }

/--
Theorem 7.9.8. If $z_0 \in \mathbb{C}$ and $A \in \mathbb{C}^{n \times n}$, then

$$
\operatorname{dist}\left(z_0, \Lambda_\epsilon(A)\right) \geq \frac{1}{\left\|\left(z_0 I-A\right)^{-1}\right\|_2} - \epsilon .
$$
-/
theorem pseudospectrum_distance_lower_bound {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ)
    (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    Metric.infDist z₀ (pseudospectrum A ε) ≥ 1 / ‖(z₀ • 1 - A)⁻¹‖ - ε := by
  sorry

end NAlg_P30



namespace NAlg_P31

attribute [instance] instL2OpNormedAddCommGroup

/-- `singularValues A i` is the `i`-th singular value (0-based) of a real matrix `A`.
It is defined as the square root of the `i`-th (decreasingly ordered) eigenvalue of
the symmetric Gram matrix `Aᴴ * A`. -/
noncomputable def singularValues {m p : ℕ} [NeZero m] [NeZero p] (A : Matrix (Fin m) (Fin p) ℂ) :
    Fin p → ℝ := by
  set M : Matrix (Fin p) (Fin p) ℂ := Aᴴ * A
  have hM : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hT : (toEuclideanLin M).IsSymmetric :=
    isHermitian_iff_isSymmetric.mp hM
  exact fun i ↦ Real.sqrt (LinearMap.IsSymmetric.eigenvalues hT (by simp) i)

noncomputable def minimum_singular_value {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  singularValues A ⟨n - 1, Nat.sub_one_lt (NeZero.ne' n).symm⟩

/--
P6.5.4 Assume that

$$
A=\left[\begin{array}{cc}
R & H \\
0 & E
\end{array}\right], \quad \rho=\frac{\|E\|_2}{\sigma_{\min }(R)}<1,
$$

where $R$ and $E$ are square. Show that if

$$
Q=\left[\begin{array}{ll}
Q_{11} & Q_{12} \\
Q_{21} & Q_{22}
\end{array}\right]
$$

is orthogonal and

$$
\left[\begin{array}{cc}
R & H \\
0 & E
\end{array}\right]\left[\begin{array}{ll}
Q_{11} & Q_{12} \\
Q_{21} & Q_{22}
\end{array}\right]=\left[\begin{array}{cc}
R_1 & 0 \\
H_1 & E_1
\end{array}\right],
$$

then $\left\|H_1\right\|_2 \leq \rho\|H\|_2$.
-/
theorem orthogonal_transform_block_norm_bound {n p : ℕ} [NeZero n] [NeZero p]
    (R : Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin n) (Fin p) ℝ) (E : Matrix (Fin p) (Fin p) ℝ)
    (ρ : ℝ) (hρ : ρ = ‖E‖ / minimum_singular_value (R.map (algebraMap ℝ ℂ))) (hlt : ρ < 1)
    (Q : Matrix ((Fin n) ⊕ (Fin p)) ((Fin n) ⊕ (Fin p)) ℝ)
    (hQ : Q ∈ orthogonalGroup ((Fin n) ⊕ (Fin p)) ℝ) (R₁ : Matrix (Fin n) (Fin n) ℝ)
    (H₁ : Matrix (Fin p) (Fin n) ℝ) (E₁ : Matrix (Fin p) (Fin p) ℝ) :
    fromBlocks R H 0 E * Q = fromBlocks R₁ 0 H₁ E₁ → ‖H₁‖ ≤ ρ * ‖H‖ := by
  sorry

end NAlg_P31



namespace NAlg_P32

/--
P8.4.8 Suppose that

$$
A=\left[\begin{array}{cc}
D & v \\
v^T & d_n
\end{array}\right]
$$

where $D=\operatorname{diag}\left(d_1, \ldots, d_{n-1}\right)$ has distinct diagonal entries and $v \in \mathbb{R}^{n-1}$ has no zero entries.

(a) Show that if $\lambda \in \lambda(A)$, then $D-\lambda I_{n-1}$ is nonsingular.
-/
theorem diagonal_plus_rank_one_eigenvalue_condition (n : ℕ) (hn : n > 0) (d : Fin (n - 1) → ℝ)
    (v : Fin (n - 1) → ℝ) (d_n : ℝ) (h_distinct : d.Injective) (h_nonzero : ∀ i, v i ≠ 0)
    (A : Matrix (Fin (n - 1) ⊕ Fin 1) (Fin (n - 1) ⊕ Fin 1) ℝ)
    (hA : A = fromBlocks (diagonal d) (fun i j ↦ v i) (fun i j ↦ v j) (fun _ _ => d_n)) :
    ∀ μ, Module.End.HasEigenvalue (toLin' A) μ → IsUnit (diagonal d - μ • 1) := by
  sorry

/--
(b) Show that if $\lambda \in \lambda(A)$, then $\lambda$ is a zero of

$$
f(\lambda)=\lambda+\sum_{k=1}^{n-1} \frac{v_k^2}{d_k-\lambda}-d_n .
$$
-/
theorem eigenvalue_equation_for_diagonal_plus_rank_one (n : ℕ) (hn : n > 0) (d : Fin (n - 1) → ℝ)
    (v : Fin (n - 1) → ℝ) (d_n : ℝ) (h_distinct : d.Injective) (h_nonzero : ∀ i, v i ≠ 0)
    (A : Matrix (Fin (n - 1) ⊕ Fin 1) (Fin (n - 1) ⊕ Fin 1) ℝ)
    (hA : A = fromBlocks (diagonal d) (fun i j ↦ v i) (fun i j ↦ v j) (fun _ _ => d_n)) :
    ∀ μ, Module.End.HasEigenvalue (toLin' A) μ → μ + ∑ k, (v k)^2 / (d k - μ) - d_n = 0 := by
  sorry

end NAlg_P32
