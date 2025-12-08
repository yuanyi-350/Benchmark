import Mathlib

open Matrix WithLp



namespace NAlg_A7

open scoped Norms.Frobenius

variable {m n : ℕ} [NeZero m] [NeZero n]

def algorithm  (A B : Matrix (Fin m) (Fin n) ℝ) (hA : rank A = n) :
    ℕ → Matrix (Fin n) (Fin n) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

/--
P6.4.5 Suppose $A, B \in \mathbb{R}^{m \times n}$ and that $A$ has full column rank.
Show how to compute a symmetric matrix $X \in \mathbb{R}^{n \times n}$ that minimizes $\|A X-B\|_F$. Hint: Compute the SVD of $A$.
-/
theorem exists_symmetric_frobenius_minimizer (A B : Matrix (Fin m) (Fin n) ℝ) (hA : rank A = n) :
    IsSymm (algorithm A B hA m) ∧
    IsMinOn (fun (X : Matrix (Fin n) (Fin n) ℝ) ↦ ‖A * X - B‖) ⊤ (algorithm A B hA m) := by
  sorry

end NAlg_A7



namespace NAlg_A8

variable {n : ℕ} [NeZero n]

def algorithm (x y : Fin n → ℝ) : ℝ × ℝ := by
  sorry

theorem square_add_eq_one (x y : Fin n → ℝ) :
    (algorithm x y).1 ^ 2 + (algorithm x y).2 ^ 2 = 1 := by
  sorry

/--
P8.6.6 Let $x$ and $y$ be in $\mathbb{R}^m$ and define the orthogonal matrix $Q$ by

$$
Q=\left[\begin{array}{rr}
c & s \\
-s & c
\end{array}\right] .
$$

Give a stable algorithm for computing $c$ and $s$ such that the columns of $[x \mid y] Q$ are orthogonal to each other.
-/
theorem exists_orthogonal_Q_make_columns_orthogonal (x y : Fin n → ℝ) : inner ℝ
    (toLp 2 ((algorithm x y).1 • x - (algorithm x y).2 • y))
    (toLp 2 ((algorithm x y).2 • x + (algorithm x y).1 • y)) = 0 := by
  sorry

end NAlg_A8



namespace NAlg_A9

variable {n : ℕ} [NeZero n]

def Hessenberg (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (j.1 + 2 ≤ i.1) → H i j = 0

def algorithm (A B : Matrix (Fin n) (Fin n) ℝ) :
    ℕ → (Matrix (Fin n) (Fin n) ℝ) × (Matrix (Fin n) (Fin n) ℝ) := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

/--
P7.7.2 Suppose $A$ and $B$ are in $\mathbb{R}^{n \times n}$. Give an algorithm for computing orthogonal $Q$ and $Z$ such that $Q^T A Z$ is upper Hessenberg and $Z^T B Q$ is upper triangular.
-/
theorem exists_orthogonal_QZ_hessenberg_and_triangular (A B : Matrix (Fin n) (Fin n) ℝ) :
    (algorithm A B n).1 ∈ orthogonalGroup (Fin n) ℝ ∧
    (algorithm A B n).2 ∈ orthogonalGroup (Fin n) ℝ ∧
    Hessenberg ((algorithm A B n).1ᵀ * A * (algorithm A B n).2) ∧
    ((algorithm A B n).2ᵀ * A * (algorithm A B n).1).BlockTriangular id:= by
  sorry

end NAlg_A9



namespace NAlg_A10

variable {m n p : ℕ} [NeZero m] [NeZero n] [NeZero p]

variable{A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin p) (Fin n) ℝ}

def algorithm (hA : rank A = n) (hB : rank B = p) (b : Fin m → ℝ) : Fin n → ℝ := by
  sorry

/--
P6.3.6 If $A \in \mathbb{R}^{m \times n}$ has full column rank and
$B \in \mathbb{R}^{p \times n}$ has full row rank,
show how to minimize $$ f(x)=\frac{\|A x-b\|_2^2}{1+x^T x} $$ subject to the constraint that $B x=0$.
-/
theorem exists_minimizer_under_constraint (b : Fin m → ℝ) (hA : rank A = n) (hB : rank B = p) :
    (algorithm hA hB b) ∈ {x | B *ᵥ x = 0} ∧
    IsMinOn (fun (x : Fin n → ℝ) ↦ ‖toLp 2 (A *ᵥ x - b)‖^2 / (1 + ‖toLp 2 x‖ ^ 2))
    {x | B *ᵥ x = 0} (algorithm hA hB b) := by
  sorry

end NAlg_A10



namespace NAlg_A11

variable {m n : ℕ} [NeZero n] [NeZero m]

def leadingBlock (L : Matrix (Fin m) (Fin n) ℝ) (hmn : n ≤ m) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => L (Fin.castLEEmb hmn i) j

def leadingBlockLowerTriangular (L : Matrix (Fin m) (Fin n) ℝ) (hmn : n ≤ m) : Prop :=
  (leadingBlock (L := L) hmn).BlockTriangular OrderDual.toDual

def algorithm (A : Matrix (Fin m) (Fin n) ℝ) : ℕ → Matrix (Fin m) (Fin m) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

/--
P5.4.4 Suppose $A \in \mathbb{R}^{m \timesf n}$ with $m \geq n$.
Give an algorithm that uses Householder matrices to compute an orthogonal $Q \in \mathbb{R}^{m \times m}$
so that if $Q^T A=L$, then $L(n+1: m,:)=0$ and $L(1: n, 1: n)$ is lower triangular.
-/
theorem exists_householder_Q (A : Matrix (Fin m) (Fin n) ℝ) (hmn : n ≤ m) :
    algorithm A m ∈ orthogonalGroup (Fin m) ℝ ∧
    ∀ i : Fin m, n ≤ (i : ℕ) → ∀ j : Fin n, ((algorithm A m)ᵀ * A) i j = 0 ∧
    leadingBlockLowerTriangular ((algorithm A m)ᵀ * A) hmn := by
  sorry

end NAlg_A11



namespace NAlg_A12

variable {n : ℕ} [NeZero n] {S : Matrix (Fin n) (Fin n) ℝ}

/--
A matrix is tridiagonal when every entry more than one step away from the main
diagonal is zero.
-/
def IsTridiagonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (i j : Fin n), 1 < Nat.dist (i : ℕ) (j : ℕ) → M i j = 0

def algorithm (hS_skew : Sᵀ = -S) (u : Fin n → ℝ) (σ : ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

/--
P8.4.5 Suppose $A=S+\sigma u u^T$ where $S \in \mathbb{R}^{n \times n}$ is skew-symmetric,
$u \in \mathbb{R}^n$, and $\sigma \in \mathbb{R}$.
Show how to compute an orthogonal $Q$ such that $Q^T A Q=T+\sigma e_1 e_1^T$ where $T$ is tridiagonal and skew-symmetric.
-/
theorem exists_orthogonal_Q_tridiagonal_skew (hS_skew : Sᵀ = -S) (u : Fin n → ℝ) (σ : ℝ) :
    (algorithm hS_skew u σ n) ∈ orthogonalGroup (Fin n) ℝ ∧
    ∃ (T : Matrix (Fin n) (Fin n) ℝ), IsTridiagonal T ∧ Tᵀ = -T ∧
    (algorithm hS_skew u σ n)ᵀ * (S + σ • vecMulVec u u) * (algorithm hS_skew u σ n)
    = T + σ • vecMulVec (fun (i : Fin n) => if (i : ℕ) = 0 then 1 else 0)
    (fun (i : Fin n) => if (i : ℕ) = 0 then 1 else 0) := by
  sorry

end NAlg_A12



namespace NAlg_A13

variable {n : ℕ} [NeZero n] {S : Matrix (Fin n) (Fin n) ℝ} {u : Fin n → ℝ}

/--
A matrix is tridiagonal when every entry more than one step away from the main
diagonal is zero.
-/
def IsTridiagonal (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (i j : Fin n), 1 < Nat.dist (i : ℕ) (j : ℕ) → M i j = 0

def algorithm (hS_skew : Sᵀ = -S) (hu_norm : ‖u‖ = 1) (σ : ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ := fun k => match k with
  | 0 => 0
  | k + 1 => sorry

/--
P8.3.7 Suppose $A=S+\sigma u u^T$ where $S \in \mathbb{R}^{n \times n}$ is skew-symmetric
$\left(S^T=-S\right), u \in \mathbb{R}^n$ has unit 2-norm, and $\sigma \in \mathbb{R}$.
Show how to compute an orthogonal $Q$ such that $Q^T A Q$ is tridiagonal and $Q^T u=e_1$.
-/
theorem exists_orthogonal_Q_tridiagonal (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ)
    (hA : A = S + σ • vecMulVec u u) (hS_skew : Sᵀ = - S) (hu_norm : ‖u‖ = 1) :
    (algorithm hS_skew hu_norm σ n) ∈ orthogonalGroup (Fin n) ℝ ∧
    IsTridiagonal ((algorithm hS_skew hu_norm σ n)ᵀ * A * (algorithm hS_skew hu_norm σ n)) ∧
    (algorithm hS_skew hu_norm σ n)ᵀ *ᵥ u = fun (i : Fin n) => if (i : ℕ) = 0 then 1 else 0 := by
  sorry

end NAlg_A13



namespace NAlg_A14

open scoped Matrix.Norms.Frobenius

variable {n : ℕ} [NeZero n]

def algorithm (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := by
  sorry

def admissible (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  rank S = 2 ∧ Sᵀ = -S

/--
P8.1.13 Give an algorithm for computing the solution to

$$
\min_{\substack{\operatorname{rank}(S)=2 \\ S=-S^T}}\|A-S\|_F .
$$
-/
theorem exists_best_rank2_skew_approx (A : Matrix (Fin n) (Fin n) ℝ) :
    (algorithm A) ∈ {S | rank S = 2 ∧ Sᵀ = -S} ∧
    IsMinOn (fun S ↦ ‖A - S‖) {S | rank S = 2 ∧ Sᵀ = -S} (algorithm A) := by
  sorry

end NAlg_A14



namespace NAlg_A15

open scoped Matrix.Norms.Frobenius

variable {n : ℕ} [NeZero n]

def algorithm (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := by
  sorry

def admissible (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  rank S = 2 ∧ Sᵀ = -S

/--
P8.1.12 Give an algorithm for computing the solution to

$$
\min_{\underset{S=S^T}{\operatorname{rank}(S)=1}}\|A-S\|_F .
$$
-/
theorem exists_best_rank2_skew_approx (A : Matrix (Fin n) (Fin n) ℝ) :
    (algorithm A) ∈ {S | rank S = 1 ∧ Sᵀ = S} ∧
    IsMinOn (fun S ↦ ‖A - S‖) {S | rank S = 1 ∧ Sᵀ = S} (algorithm A) := by
  sorry

end NAlg_A15
