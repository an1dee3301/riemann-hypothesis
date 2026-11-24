module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAvgLinear
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTranslate
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCompAddEquivEqSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOExtXExtY
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
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
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
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
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

namespace I195MixedCoordinates_b25480cef10b1759a6cbdced

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

end I195MixedCoordinates_b25480cef10b1759a6cbdced

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitPlaceForm


set_option maxHeartbeats 1000000 in
theorem exists_form_of_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧ ∀ (h : GL (Fin T.rank) (AE D)) (a : GL (Fin ρ) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ (f f' : WO S T → ℂ) (k : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 (f') x) = k * ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 (f) (h.1 ⬝ x ⬝ a.1))) → ℓ f' = r * k * ℓ f := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 hne
  letI : MeasurableSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.measHalf _ _ _
  haveI : BorelSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.borelHalf _ _ _
  have hH : ∀ x, x ∈ GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ ↔ ∀ i j, cA D e * x i j = x i j := fun x => Iff.rfl
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.HalfLinForm.halfAvg_linear D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun h a => ?_⟩
  · rw [hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u), hℓ f hf]
    exact GlobalTheory.HalfInvariance.half_avg_heis_inv D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 _ hH _ u hu f hf
  · obtain ⟨f, hf, hn⟩ := GlobalTheory.HalfNonvan.avg_mixS_ne_zero D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hne _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
    exact ⟨f, hf, by rw [hℓ f hf]; exact hn⟩
  · obtain ⟨r, hr, hm⟩ := GlobalTheory.HalfTwist.integral_twist_fix_eq_smul D T.rank ρ (cA D e) _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ) h a
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    have e1 := hm fun x => ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 f x)
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← e1, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)

end GlobalTheory.SplitPlaceForm
