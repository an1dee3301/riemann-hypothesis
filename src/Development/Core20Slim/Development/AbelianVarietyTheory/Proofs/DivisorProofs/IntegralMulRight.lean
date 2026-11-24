module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling   GlobalTheory.MixModel  
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RightMulJac

theorem integral_mul_right : ∀ (D : D7) (t n : ℕ) (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)),
    IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
    ∀ (a : GL (Fin n) (AE D)) (f : Mx D t n → ℂ),
      ∫ x, f (x ⬝ a.1) ∂μ₁ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(t : ℂ)) * ∫ x, f x ∂μ₁ := by
  intro D t n μ₁ 𝓕₁ hμ a f
  haveI : μ₁.IsAddHaarMeasure := hμ.1
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  have hkey := GlobalTheory.ModuLR.modu_lrMul D t n μ₁ hμ.1 1 a
  simp only [map_one, one_pow, one_mul, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, ENNReal.coe_one] at hkey
  set c : ℝ≥0 := absA D (Matrix.GeneralLinearGroup.det a) with hc
  have hc0 : c ≠ 0 := by
    exact ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  have hcont : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n) := continuous_id.matrix_mul continuous_const
  have hcont' : Continuous fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n) := continuous_id.matrix_mul continuous_const
  let e : Mx D t n ≃ₜ Mx D t n :=
    { toFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)
      invFun := fun u => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) (a⁻¹).val : Mx D t n)
      left_inv := fun u => by simp [Matrix.mul_assoc]
      right_inv := fun u => by simp [Matrix.mul_assoc]
      continuous_toFun := hcont
      continuous_invFun := hcont' }
  have hemb : MeasurableEmbedding (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) := e.measurableEmbedding
  have hmap : μ₁.map (fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) = ((c : ENNReal) ^ t)⁻¹ • μ₁ := by
    conv_rhs => rw [hkey]
    rw [smul_smul, ENNReal.inv_mul_cancel (by simp [hc0]) (by simp), one_smul]
  rw [show (∫ x, f (x ⬝ a.1) ∂μ₁) = ∫ x, f ((fun u : Mx D t n => (HMul.hMul (u : Matrix (Fin t) (Fin n) (AE D)) a.val : Mx D t n)) x) ∂μ₁ from rfl,
    ← hemb.integral_map, hmap, integral_smul_measure]
  rw [Complex.real_smul, npow]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.coe_toReal,
    show (-(t : ℂ)) = ((-(t : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (NNReal.coe_nonneg c), Real.rpow_neg (NNReal.coe_nonneg c), Real.rpow_natCast]

end GlobalTheory.RightMulJac

end
