module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedIntegralDecompContinuousPeriodic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
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
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedIntegral_decomp_continuous_periodic : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ r ∈ GlobalTheory.MixModel.ratMx D a b, f₁ r ∈ ratL W V) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → Continuous (fun s => ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∧ ∀ r ∈ GlobalTheory.MixModel.ratMx D a b, ∀ s, ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ (r + s) + f₂ z + f₃ y) ∂μ) ∂η = ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η := by
  first | exact @GlobalTheory.IsoMean.iterInt_continuous_periodic | exact GlobalTheory.IsoMean.iterInt_continuous_periodic | (intros; apply GlobalTheory.IsoMean.iterInt_continuous_periodic <;> assumption)
