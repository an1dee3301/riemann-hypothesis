module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

namespace I195MixedCoordinates_784daf8855fd46d1374640e6

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_784daf8855fd46d1374640e6

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.FlatHeis

theorem flatAt_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x y = heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x y)) ∧ (∀ w, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) = heisO ψ V₀ W₀ w (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ)) ∧ ∀ γ, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ (ratW W₀ V₀ γ) = flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x y Ψ hΨ
  have hMV := GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ
  have hHT := GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ
  have hS : ∀ x', IsThetaFunO ψ V₀ W ((_root_.I195MixedCoordinates_784daf8855fd46d1374640e6.source dV) W ψ vS.μ vS.𝓕 Ψ x') := fun x' =>
    hMV.1 V V₀ W ρ dV vS.μ vS.𝓕 vS.covol Ψ hΨ x'
  have hE : ∀ x', IsThetaFunO ψ V₀ W₀ (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := fun x' =>
    hMV.2 V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x') y
  have h1 : ∀ x' w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x' y =
      heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := by
    intro x' w
    have a := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ V V₀ W ρ dV vS Ψ hΨ).2.2.1 x' (dW.inc0 V₀ w)
    have b := (hHT V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x')).2.1 w y
    change I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕
      (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x' =
      heisO ψ V₀ W (dW.inc0 V₀ w)
        (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕 Ψ x') at a
    change I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ vT.μ vT.𝓕
      (heisO ψ V₀ W (dW.inc0 V₀ w)
        (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕 Ψ x')) y =
      heisO ψ V₀ W₀ w (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ vT.μ vT.𝓕
        (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕 Ψ x') y) at b
    unfold evalAt
    rw [a, b]
  refine ⟨fun w => h1 x w, fun w => ?_, fun γ => ?_⟩
  · funext w'
    show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) w' u ∂vU.ν =
      ψ (symplOH V₀ W₀ w' w) * ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (w' + w) u ∂vU.ν
    rw [← integral_const_mul]
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    simp only [flatFun, h1, heisO]
    ring
  · show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (ratW W₀ V₀ γ) u ∂vU.ν =
      ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ 0 u ∂vU.ν
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    have q := (hE (x ⬝ u.1.1)).quasi γ 0
    rw [add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at q
    unfold flatFun
    rw [q]

end GlobalTheory.FlatHeis

end
