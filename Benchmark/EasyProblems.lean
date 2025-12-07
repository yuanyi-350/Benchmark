import Mathlib

open Matrix



namespace NAlg_E1

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem eq_145 (A : Matrix n n ℂ)(h : IsUnit A.det) : A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 :=
  sorry

end NAlg_E1



namespace NAlg_E2

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem eq_151 (A : Matrix n n ℂ) : A⁻¹ = (1 / A.det) • adjugate A := by
  sorry

end NAlg_E2



namespace NAlg_E3

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem eq_156 (A : Matrix n n ℂ) (B : Matrix m m ℂ) (C : Matrix n m ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (h : IsUnit (B⁻¹ + Cᵀ*A⁻¹*C)) :
    (A + C * B * Cᵀ)⁻¹ = A⁻¹ - A⁻¹ * C * (B⁻¹ + Cᵀ*A⁻¹*C)⁻¹ * Cᵀ * A⁻¹ :=
  sorry

end NAlg_E3



namespace NAlg_E4

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem eq_159 (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (hA : IsUnit A) (h : IsUnit (1 + C * A⁻¹ * B)) :
    (A + B * C)⁻¹ = A⁻¹ - A⁻¹ * B * (1 + C * A⁻¹ * B)⁻¹ * C * A⁻¹ := by
  sorry

end NAlg_E4



namespace NAlg_E5

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem eq_163 (A B : Matrix n n ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    (A⁻¹ + B⁻¹)⁻¹ = A * (A + B)⁻¹ * B ∧ (A⁻¹ + B⁻¹)⁻¹ = B * (A + B)⁻¹ * A := by
  sorry

end NAlg_E5


namespace NAlg_E6

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem eq_16 {A : Matrix m n ℝ} {B : Matrix n p ℝ} {C : Matrix p m ℝ} :
    trace (A * B * C) = trace (B * C * A) := by
  sorry

end NAlg_E6
