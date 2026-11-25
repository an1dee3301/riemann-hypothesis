module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPow
public import Formalism.PairingDivisors.StatementA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ), IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.HeckeLBound.norm_heckeL_le | exact GlobalTheory.HeckeLBound.norm_heckeL_le | (intros; apply GlobalTheory.HeckeLBound.norm_heckeL_le <;> assumption)
