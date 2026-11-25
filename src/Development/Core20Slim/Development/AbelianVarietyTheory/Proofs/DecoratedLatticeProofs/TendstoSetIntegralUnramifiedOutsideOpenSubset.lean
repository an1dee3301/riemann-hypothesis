module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.List
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem measurableSet_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) (S : Finset (FinPl D)) :
    MeasurableSet (openOff A L S) := by
  have : BorelSpace (GA D A) := ⟨rfl⟩
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  have e : openOff A L S = ⋂ v, ⋂ (_ : v ∉ S),
      (proj D.sp.cm.sig A.gram v) ⁻¹' (stabLoc D.sp.cm.sig A.gram L v : Set _) := by
    ext g; simp [openOff]
  rw [e]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    ((isOpen_stabLoc D.sp.cm.sig A.gram L v).preimage (continuous_proj D.sp.cm.sig A.gram v)).measurableSet

theorem monotone_openOff {D : D7} (A : HSp D) (L : Lat A) : Monotone (openOff A L) :=
  fun _ _ h _ hg v hv => hg v fun h' => hv (h h')

theorem iUnion_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) : ⋃ S, openOff A L S = Set.univ := by
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  refine Set.eq_univ_of_forall fun g => ?_
  have h := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig A.gram L g)
  exact Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => by_contra fun h' => hv (h.mem_toFinset.2 h')⟩

theorem tendsto_setIntegral_openOff : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)) (F : GA D A → ℂ), Integrable F m → Filter.Tendsto (fun S : Finset (FinPl D) => ∫ g in openOff A L S, F g ∂m) Filter.atTop (nhds (∫ g, F g ∂m)) := by
  intro D A L hL m F hF
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  have h := tendsto_setIntegral_of_monotone (μ := m) (f := F) (measurableSet_openOff A L hL) (monotone_openOff A L)
    hF.integrableOn
  rwa [iUnion_openOff A L hL, Measure.restrict_univ] at h

end GlobalTheory.Core.Rk.IP

end
