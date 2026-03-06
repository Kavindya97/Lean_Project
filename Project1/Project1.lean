import Mathlib

open Matrix BigOperators

noncomputable section

namespace LeastSquares

variable {m n : Type*}
variable [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

def residual (A : Matrix m n ℝ) (f : m → ℝ) (x : n → ℝ) : m → ℝ :=
  f - A.mulVec x

def Phi (A : Matrix m n ℝ) (f : m → ℝ) (x : n → ℝ) : ℝ :=
  ‖residual A f x‖ ^ 2

def IsLeastSquares (A : Matrix m n ℝ) (f : m → ℝ) (x : n → ℝ) : Prop :=
  ∀ y : n → ℝ, Phi A f x ≤ Phi A f y

def NormalEq (A : Matrix m n ℝ) (f : m → ℝ) (x : n → ℝ) : Prop :=
  (A.transpose.mulVec (A.mulVec x)) = A.transpose.mulVec f

end LeastSquares
