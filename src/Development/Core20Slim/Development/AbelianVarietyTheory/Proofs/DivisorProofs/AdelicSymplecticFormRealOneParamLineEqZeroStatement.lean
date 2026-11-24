module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticFormRealOneParamLineEqZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  first | exact @GlobalTheory.ThetaTransform.symV_realLine_eq_zero | exact GlobalTheory.ThetaTransform.symV_realLine_eq_zero | (intros; apply GlobalTheory.ThetaTransform.symV_realLine_eq_zero <;> assumption)
