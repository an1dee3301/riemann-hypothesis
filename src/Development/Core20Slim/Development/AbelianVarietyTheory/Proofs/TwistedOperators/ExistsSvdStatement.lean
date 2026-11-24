module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ), ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ, B = U * (Matrix.of fun (i : Fin p) (j : Fin q) => if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  first | exact @GlobalTheory.RectSVD.exists_svd | exact GlobalTheory.RectSVD.exists_svd | (intros; apply GlobalTheory.RectSVD.exists_svd <;> assumption)
