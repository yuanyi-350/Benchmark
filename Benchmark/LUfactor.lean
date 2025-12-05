import Mathlib

open Matrix

noncomputable section

variable {n : ℕ}

def gaussNudge (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  vecMulVec
    (fun i => if k < i then U i k / U k k else 0)
    (fun j => if j = k then (1 : ℝ) else 0)

def gaussElim (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  1 - gaussNudge U k

def gaussElimInv (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  1 + gaussNudge U k

abbrev LowerTriangular (M : Matrix (Fin n) (Fin n) ℝ) : Prop := BlockTriangular M OrderDual.toDual

lemma gaussNudge_sq (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    gaussNudge U k * gaussNudge U k = 0 := by
  ext i j
  have : (fun x : Fin n => gaussNudge U k i x * gaussNudge U k x j) = fun _ => (0 : ℝ) := by
    funext x
    simp [gaussNudge, vecMulVec]
    grind
  simp [mul_apply, this]

lemma gaussElimInv_mul_gaussElim (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    gaussElimInv U k * gaussElim U k = 1 := by
  simp [gaussElim, gaussElimInv, sub_eq_add_neg, mul_add, add_mul, gaussNudge_sq U k]

def lufactor (A : Matrix (Fin n) (Fin n) ℝ) : ℕ →
    Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
  | 0 => (1, A)
  | k + 1 =>
    if hk : k < n then ((lufactor A k).1 * gaussElimInv (lufactor A k).2 ⟨k, hk⟩,
      gaussElim (lufactor A k).2 ⟨k, hk⟩ * (lufactor A k).2)
    else lufactor A k

lemma lufactor_mul (A : Matrix (Fin n) (Fin n) ℝ) : ∀ k, (lufactor A k).1 * (lufactor A k).2 = A
  | 0 => by simp [lufactor]
  | k + 1 => by
    by_cases hk : k < n
    · have h := lufactor_mul (A := A) k
      simp [lufactor, hk] at h ⊢
      calc
        _ = (lufactor A k).1 * ((gaussElimInv (lufactor A k).2 ⟨k, hk⟩ *
            gaussElim (lufactor A k).2 ⟨k, hk⟩) * (lufactor A k).2) := by
          simp [mul_assoc]
        _ = (lufactor A k).1 * (lufactor A k).2 := by
          simp [gaussElimInv_mul_gaussElim]
        _ = A := h
    · simp [lufactor, hk, lufactor_mul]

lemma gaussNudge_upper_zero (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    ∀ ⦃i j⦄, i < j → gaussNudge U k i j = 0 := by
  intro i j hij
  by_cases hkj : j = k
  · have hklt : ¬ k < i := not_lt.mpr (by omega)
    simp [gaussNudge, vecMulVec, hklt]
  · simp [gaussNudge, vecMulVec, hkj]

lemma gaussElim_lower (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    LowerTriangular (gaussElim U k) := by
  intro i j hij
  have hij' : i < j := by simpa using hij
  simp [gaussElim, gaussNudge_upper_zero U k hij', hij'.ne]

lemma gaussElimInv_lower (U : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    LowerTriangular (gaussElimInv U k) := by
  intro i j hij
  have hij' : i < j := by simpa using hij
  simp [gaussElimInv, gaussNudge_upper_zero U k hij', hij'.ne]

lemma lower_mul {A B : Matrix (Fin n) (Fin n) ℝ} (hA : LowerTriangular A) (hB : LowerTriangular B) :
    LowerTriangular (A * B) := by
  simpa [LowerTriangular] using
    (BlockTriangular.mul (b := OrderDual.toDual) (M := A) (N := B) hA hB)

lemma lufactor_lower_triangular (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ k, LowerTriangular (lufactor A k).1 := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      simp at hij
      simp [lufactor, hij.ne]
  | succ k ih =>
      by_cases hk : k < n
      · simpa [lufactor, hk] using lower_mul ih (gaussElimInv_lower (lufactor A k).2 ⟨k, hk⟩)
      ·simpa [lufactor, hk] using ih

abbrev UpperTriangular (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=BlockTriangular M id

def UpperEliminated (k : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ ⦃i j : Fin n⦄, j < i → j.1 < k → U i j = 0

lemma gaussElim_mul_apply (U : Matrix (Fin n) (Fin n) ℝ) (k i j : Fin n) : (gaussElim U k * U) i j =
      U i j - (if k < i then U i k / U k k else 0) * U k j := by
  have hmul : (gaussNudge U k * U) i j = (if k < i then U i k / U k k else 0) * U k j := by
    simp [gaussNudge, Matrix.mul_apply, vecMulVec]
  simp [← hmul, gaussElim, sub_mul]

lemma upperElim_step (A : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hk : k < n)
    (hU : UpperEliminated k ((lufactor A k).2)) (hpivot : (lufactor A k).2 ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0) :
    UpperEliminated (k.succ) ((gaussElim (lufactor A k).2 ⟨k, hk⟩) * (lufactor A k).2) := by
  intro i j hlt hjlt
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hjlt) with hjlt' | hjEq
  · have : (lufactor A k).2 i j = 0 := hU hlt hjlt'
    have : (lufactor A k).2 ⟨k, hk⟩ j = 0 := hU (by omega) hjlt'
    grind [gaussElim_mul_apply]
  · have : j = (⟨k, hk⟩ : Fin n) := Fin.eq_mk_iff_val_eq.mpr hjEq
    have : (⟨k, hk⟩ : Fin n) < i := by omega
    grind [gaussElim_mul_apply]

lemma lufactor_triangular (A : Matrix (Fin n) (Fin n) ℝ)
    (hpivot : ∀ k : Fin n, (lufactor A k).2 k k ≠ 0) : UpperTriangular (lufactor A n).2 :=
  have (k : ℕ) : UpperEliminated k ((lufactor A k).2) := by
    induction k with
    | zero => exact fun i j hlt hjlt ↦ (Nat.not_lt_zero _ hjlt).elim
    | succ k ih =>
        by_cases hk : k < n
        · simpa [lufactor, hk] using upperElim_step (A := A) (hk := hk) ih (hpivot ⟨k, hk⟩)
        · intro i j hlt hjlt
          simpa [lufactor, hk] using ih hlt (by omega)
  fun i j hlt ↦ (this n) hlt j.is_lt

end
