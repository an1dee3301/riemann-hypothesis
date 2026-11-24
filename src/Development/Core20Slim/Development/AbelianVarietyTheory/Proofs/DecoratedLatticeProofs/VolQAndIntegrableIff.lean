module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.ProjectiveLattices.IsProbabilityMeasureAutQuotientNormalized
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuotFundDom

theorem volQ_and_integrable_iff : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν = (ν X).toReal ∧ ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → (Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F) (GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) ↔ IntegrableOn F X ν) := by
  intro D V ν X hν hX
  refine ⟨?_, fun F hF _ => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, Measure.real, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hX]
  · have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
    rw [← memLp_one_iff_integrable, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hX, hL.lift_descend,
      memLp_one_iff_integrable]
    rfl

end GlobalTheory.QuotFundDom
