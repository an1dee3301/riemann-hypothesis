module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernels
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
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
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels : ∀ (D : D7) (A B : HSp D) (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ K₁ K₂ : GA D A → GA D B → ℂ, (∀ K ∈ ({K₁, K₂} : Set (GA D A → GA D B → ℂ)), Continuous (Function.uncurry K) ∧ (∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) ∧ (∀ g, MemL2Quotient (GQ B) mH (K g)) ∧ (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) ∧ ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) → ∀ u₁ u₂ : GA D A → ℂ, GlobalTheory.Grow.RapidDec A u₁ → GlobalTheory.Grow.RapidDec A u₂ → let θ₁ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₁ g h * u₁ g) q ∂autMeasure A m; let θ₂ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₂ g h * u₂ g) q ∂autMeasure A m; (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₁ g h * u₁ g) (autMeasure A m)) ∧ (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₂ g h * u₂ g) (autMeasure A m)) ∧ MemL2Quotient (GQ B) mH θ₁ ∧ MemL2Quotient (GQ B) mH θ₂ ∧ petersson B mH θ₁ θ₂ = ∫ q : AutQ A × AutQ A, petersson B mH (K₁ q.1.out) (K₂ q.2.out) * u₁ q.1.out * conj (u₂ q.2.out) ∂(autMeasure A m).prod (autMeasure A m) := by
  first | exact @GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | exact GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | (intros; apply GlobalTheory.Core.Rk.Seesaw.seesaw_fubini <;> assumption)
