import Mathlib

open Matrix



namespace NAlg_E1

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem mul_inv_of_isUnit (A : Matrix n n ℂ)(h : IsUnit A.det) : A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 := by
  sorry

end NAlg_E1



namespace NAlg_E2

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem inv_eq_smul_adjugate (A : Matrix n n ℂ) : A⁻¹ = (1 / A.det) • adjugate A := by
  sorry

end NAlg_E2



namespace NAlg_E3

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem inv_add_mul_conj (A : Matrix n n ℂ) (B : Matrix m m ℂ) (C : Matrix n m ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (h : IsUnit (B⁻¹ + Cᵀ * A⁻¹ * C)) :
    (A + C * B * Cᵀ) * (A⁻¹ - A⁻¹ * C * (B⁻¹ + Cᵀ * A⁻¹ * C)⁻¹ * Cᵀ * A⁻¹) = 1 := by
  sorry

end NAlg_E3



namespace NAlg_E4

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem inv_add_mul_mul_eq (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (hA : IsUnit A) (h : IsUnit (1 + C * A⁻¹ * B)) :
    (A + B * C) * (A⁻¹ - A⁻¹ * B * (1 + C * A⁻¹ * B)⁻¹ * C * A⁻¹) = 1 := by
  sorry

end NAlg_E4



namespace NAlg_E5

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem inv_add_inv_inv_eq (A B : Matrix n n ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (hAB : IsUnit (A + B)): (A⁻¹ + B⁻¹) * (A * (A + B)⁻¹ * B) = 1 := by
  sorry

end NAlg_E5



namespace NAlg_E6

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem trace_mul_cycle {A : Matrix m n ℝ} {B : Matrix n p ℝ} {C : Matrix p m ℝ} :
    trace (A * B * C) = trace (B * C * A) := by
  sorry

end NAlg_E6



namespace NAlg_E7

variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix

theorem sherman_morrison {A : Matrix n n ℝ} (hA : IsUnit A) (u v : n → ℝ) (σ : ℝ)
    (hσ : σ = 1 + dotProduct v (A⁻¹.mulVec u)) (ne : σ ≠ 0):
    (A + vecMulVec u v) * (A⁻¹ - (σ⁻¹ • (A⁻¹ * (vecMulVec u v) * A⁻¹))) = 1 := by
  sorry

end NAlg_E7
