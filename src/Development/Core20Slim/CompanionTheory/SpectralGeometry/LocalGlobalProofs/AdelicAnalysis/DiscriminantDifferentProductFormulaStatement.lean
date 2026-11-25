module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DiscriminantDifferentProductFormula
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discriminant_different_product_formula : ∀ (F : Type) [Field F] [NumberField F], (∀ᶠ v in Filter.cofinite, (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1) ∧ Real.toNNReal (Real.sqrt |(discr F : ℝ)|) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.SelfDual.sqrt_discr_mul_finprod_different | exact GlobalTheory.CompanionTheory.SW.SelfDual.sqrt_discr_mul_finprod_different | (intros; apply GlobalTheory.CompanionTheory.SW.SelfDual.sqrt_discr_mul_finprod_different <;> assumption)
