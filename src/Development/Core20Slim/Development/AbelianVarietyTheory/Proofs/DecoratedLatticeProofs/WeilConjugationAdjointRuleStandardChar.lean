module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpacesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPairStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
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
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
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
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilConjAdjoint

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7} {S T : HSp D}

theorem conjTarget_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjTarget om (g, negGA T h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjTarget] using this

theorem conjSource_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjSource om (negGA S g, h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjSource] using this

theorem conjAdjoint_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem conjAdjoint_holds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ S T : HSp D, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.ConjAdjoint ψ S T := by
  intro D ψ hψ S T
  obtain ⟨hθ, hH⟩ := GlobalTheory.T.thetaHeisenberg_conjugation_negHermitianSpace D ψ hψ S T
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T
  refine ⟨hθ, hH, fun χS χT om H => ?_, fun χS χT om H => ?_, d1, d2, d3, d4, fun χS χT om H => ?_⟩
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).1
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjTarget_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S (negSp T) _ _ om' _ H' H1 _ _ ((hθ f).1.2 hf)
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).2
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjSource_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ (negSp S) T _ _ om' _ H' H1 _ _ ((hθ f).2.2 hf)
  · have H1 := GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS χT om H
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjAdjoint_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ T S _ _ om' _ H' H1 _ _ ((d3 f).2 hf)

end GlobalTheory.WeilConjAdjoint
