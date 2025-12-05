import Mathlib

open Matrix WithLp


section MAT_1

/-
$$
\frac{\partial \operatorname{det}(\mathbf{Y})}{\partial x}=\operatorname{det}(\mathbf{Y}) \operatorname{Tr}\left[\mathbf{Y}^{-1} \frac{\partial \mathbf{Y}}{\partial x}\right]
$$
-/
theorem det_derivative_trace_formula {n : ℕ}
    (Y : ℝ → Matrix (Fin n) (Fin n) ℝ) (x : ℝ)
    (hY : IsUnit (Y x)) (hYdiff : DifferentiableAt ℝ Y x) :
    deriv (fun t => det (Y t)) x = det (Y x) * trace ((Y x)⁻¹ * deriv Y x) := by
  sorry

end MAT_1



namespace NAlg_A1

/-
P3.1.7 Suppose $L, K \in \mathbb{R}^{n \times n}$ are lower triangular and $B \in \mathbb{R}^{n \times n}$.
-/

variable {n : ℕ} {L K : Matrix (Fin n) (Fin n) ℝ} (B : Matrix (Fin n) (Fin n) ℝ)
variable (hL : L.BlockTriangular OrderDual.toDual) (hK : K.BlockTriangular OrderDual.toDual)

def algorithm (hL : L.BlockTriangular OrderDual.toDual) (hK : K.BlockTriangular OrderDual.toDual)
    (B : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

theorem algorithm_prop (B : Matrix (Fin n) (Fin n) ℝ) :
    L * algorithm hL hK B n * K = B := by
  sorry

end NAlg_A1



namespace NAlg_A2

/-
P8.3.4 Suppose $A \in \mathbb{C}^{n \times n}$ is Hermitian. Show how to construct unitary $Q$ such that $Q^H A Q=T$ is real, symmetric, and tridiagonal.
-/

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

/-- A matrix is tridiagonal when every entry more than one step away from the main
diagonal is zero. -/
def IsTridiagonal (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (i j : Fin n), 1 < Nat.dist (i : ℕ) (j : ℕ) → M i j = 0

def algorithm (hA : A.IsHermitian) : ℕ → Matrix (Fin n) (Fin n) ℂ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

theorem hermitian_unitary_tridiagonal (hA : A.IsHermitian) :
      algorithm hA n ∈ unitaryGroup (Fin n) ℂ ∧
      IsHermitian ((algorithm hA n)ᴴ * A * (algorithm hA n)) ∧
      IsSymm ((algorithm hA n)ᴴ * A * (algorithm hA n)) ∧
      ((algorithm hA n) * A * (algorithm hA n)).BlockTriangular OrderDual.toDual := sorry

end NAlg_A2



namespace NAlg_P0

/-
The famous least squares problem
-/

theorem least_squares_normal_equation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : IsMinOn (fun x ↦ ‖toLp 2 (A *ᵥ x - b)‖) ⊤ x ↔ (Aᵀ * A) *ᵥ x = Aᵀ *ᵥ b := by
  sorry

end NAlg_P0



namespace NAlg_A3

open scoped Matrix.Norms.Frobenius

/-
P7.5.2 Given $A \in \mathbb{R}^{2 \times 2}$, show how to compute a diagonal $D \in \mathbb{R}^{2 \times 2}$

so that $\left\|D^{-1} A D\right\|_F$ is minimized.
-/

variable (A : Matrix (Fin 2) (Fin 2) ℝ)

def algorithm (A : Matrix (Fin 2) (Fin 2) ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

instance algorithm_Invertible : Invertible (algorithm A 2).det := by
  sorry

theorem algorithm_prop : IsMinOn (fun (D : GL (Fin 2) ℝ) ↦ ‖D⁻¹ * A * D‖) ⊤
    (GeneralLinearGroup.mk' (algorithm A 2) (algorithm_Invertible A)) := by
  sorry

end NAlg_A3



namespace NAlg_A4

attribute [instance] instL2OpNormedAddCommGroup

/-
P11.4.2 Suppose $A \in \mathbb{R}^{n \times n}$ and $v \in \mathbb{R}^n$ are given.
How can we choose $\omega$ to minimize $\|(I-\omega A) v\|_2$ ?
-/

variable {n : ℕ}

def algorithm (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ := sorry

theorem algorithm_prop (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    IsMinOn (fun (ω : ℝ) ↦ ‖1 - ω • A‖) ⊤ (algorithm A v) := by
  sorry

end NAlg_A4



namespace NAlg_A5

open scoped Matrix.Norms.Frobenius

/-
P6.2.9(min) Suppose $r \in \mathbb{R}^m, y \in \mathbb{R}^n$, and $\delta>0$. Show how to solve the problem

$$
\min _{E \in \mathbf{R}^{m \times n},\|E\|_F \leq \delta}\|E y-r\|_2
$$
-/

variable {m n : ℕ} {δ : ℝ}

def algorithm (hδ : 0 ≤ δ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    ℕ → Matrix (Fin m) (Fin n) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

theorem algorithm_norm_le (hδ : 0 ≤ δ) (r : Fin m → ℝ) (y : Fin n → ℝ) : ‖algorithm hδ r y m‖ ≤ δ := by
  sorry

theorem zero_matrix_feasible (hδ : 0 ≤ δ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    IsMinOn (fun (E : {E : Matrix (Fin m) (Fin n) ℝ | ‖E‖ ≤ δ}) ↦
    ‖toLp 2 (E *ᵥ y - r)‖) ⊤ ⟨algorithm hδ r y m, algorithm_norm_le hδ r y⟩  := by
  sorry

end NAlg_A5


namespace NAlg_A6

open scoped Matrix.Norms.Frobenius

/-
P6.2.9(max) Suppose $r \in \mathbb{R}^m, y \in \mathbb{R}^n$, and $\delta>0$. Show how to solve the problem

$$
\max _{E \in \mathbf{R}^{m \times n},\|E\|_F \leq \delta}\|E y-r\|_2
$$
-/

variable {m n : ℕ} {δ : ℝ}

def algorithm (hδ : 0 ≤ δ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    ℕ → Matrix (Fin m) (Fin n) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

theorem algorithm_norm_le (hδ : 0 ≤ δ) (r : Fin m → ℝ) (y : Fin n → ℝ) : ‖algorithm hδ r y m‖ ≤ δ := by
  sorry

theorem zero_matrix_feasible (hδ : 0 ≤ δ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    IsMaxOn (fun (E : {E : Matrix (Fin m) (Fin n) ℝ | ‖E‖ ≤ δ}) ↦
    ‖toLp 2 (E *ᵥ y - r)‖) ⊤ ⟨algorithm hδ r y m, algorithm_norm_le hδ r y⟩  := by
  sorry

end NAlg_A6
