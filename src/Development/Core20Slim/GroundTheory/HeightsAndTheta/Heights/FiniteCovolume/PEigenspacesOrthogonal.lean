module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

theorem EigenspacesOrthogonal.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EigenspacesOrthogonal.Statement ι := by
  intro H P hMaj a b ha hb
  obtain ⟨hP, hH, hdet, -⟩ := hMaj

  have hHA : ∀ v : ι → ℂ, H *ᵥ (majInvolution H P *ᵥ v) = P *ᵥ v := by
    intro v
    rw [majInvolution, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul]

  have hmove : ∀ (M : Matrix ι ι ℂ), M.IsHermitian → ∀ u w : ι → ℂ,
      star u ⬝ᵥ (M *ᵥ w) = star (M *ᵥ u) ⬝ᵥ w := by
    intro M hM u w
    rw [star_mulVec, hM.eq, dotProduct_mulVec]
  have hPa : P *ᵥ a = H *ᵥ a := by rw [← hHA a, ha]
  have hPb : P *ᵥ b = -(H *ᵥ b) := by rw [← hHA b, hb, mulVec_neg]
  have h1 : star a ⬝ᵥ (P *ᵥ b) = star a ⬝ᵥ (H *ᵥ b) := by
    rw [hmove P hP.isHermitian, hPa, ← hmove H hH]
  have h2 : star a ⬝ᵥ (P *ᵥ b) = -(star a ⬝ᵥ (H *ᵥ b)) := by
    rw [hPb, dotProduct_neg]
  have h3 : (2 : ℂ) * (star a ⬝ᵥ (P *ᵥ b)) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h1]
    rw [h2, add_neg_cancel]
  simpa using h3

end GroundTheory.Heights₂.Heights.FiniteCovolume
