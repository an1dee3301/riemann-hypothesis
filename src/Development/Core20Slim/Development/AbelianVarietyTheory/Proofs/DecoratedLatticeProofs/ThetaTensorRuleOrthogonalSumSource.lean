module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsSumUniformLimitProductSpanStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilTensorRuleScalarEqOneStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TensorSrc

theorem op_prod {X Y : Type} (L : Module.End ℂ (X → ℂ)) (M : Module.End ℂ (Y → ℂ)) (f : X → ℂ) (g : Y → ℂ) (u : X)
    (v : Y) : L (fun u' => M (fun v' => f u' * g v') v) u = L f u * M g v := by
  have h1 : ∀ u', M (fun v' => f u' * g v') v = M g v * f u' := by
    intro u'
    have : (fun v' => f u' * g v') = f u' • g := by funext v'; simp
    rw [this, map_smul]; simp [mul_comm]
  have h2 : (fun u' => M (fun v' => f u' * g v') v) = M g v • f := by
    funext u'; simp [h1]
  rw [h2, map_smul]; simp [mul_comm]

theorem tensorSource : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S A B : HSp D) (d : OrthDec S A B) (T : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorSource ψ d T := by
  intro D ψ hψ S A B d T
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T d
  have hb : ∀ fA fB u v, d.boxS T fA fB ((d.resS T).symm (u, v)) = fA u * fB v := by
    intro fA fB u v
    simp [OrthDec.boxS]
  refine ⟨h1, h2, h3, h4, GlobalTheory.T.thetaFunctions_sum_uniform_limit_product_span D ψ hψ S A B T d, ?_, ?_⟩
  · intro χA χB χT omS omA omB hS hA hB a b h fA fB hfA hfB
    funext x
    obtain ⟨⟨u, v⟩, rfl⟩ := (d.resS T).symm.surjective x
    rw [GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h _ (h1 fA fB hfA hfB) u v, hb]
    simp only [hb]
    exact op_prod _ _ fA fB u v
  · intro χA χB χT omS omA omB hS hA hB a b h f hf v
    refine ⟨?_, fun u => GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h f hf u v⟩
    have := (h4 _ ((GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T d f hf).2 χB χT omB hB (b, h))).1 v
    simpa using this

end GlobalTheory.TensorSrc
