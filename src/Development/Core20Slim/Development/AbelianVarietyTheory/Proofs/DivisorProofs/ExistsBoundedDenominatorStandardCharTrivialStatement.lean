module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDiv
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_denominator_standardChar_trivial : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  first | exact @GlobalTheory.FinSupp.DenStd.exists_den | exact GlobalTheory.FinSupp.DenStd.exists_den | (intros; apply GlobalTheory.FinSupp.DenStd.exists_den <;> assumption)
