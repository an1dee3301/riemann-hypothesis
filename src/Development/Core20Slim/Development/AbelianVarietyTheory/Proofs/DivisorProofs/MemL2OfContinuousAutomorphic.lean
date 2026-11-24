module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Init.Tactics
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteSqInt

theorem memL2_of_continuous_definite : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → Links.IsMeasDef V K μ 𝓕 →
    ∀ u : GA D V → ℂ, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) → GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ u := by
  intro D V K μ 𝓕 hV _ hμ u hu hinv
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.2.2
  have := hμ.1.1
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D V
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hV.1 hV.2)
  have hcov' : ∀ g : GA D V, ∃ γ ∈ GQ V, γ * g ∈ C := fun g => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  refine (GlobalTheory.AutomorphicL2Unitary.memL2_iff_fundamental_domain hμ.2).2 ⟨hinv, (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2 ?_⟩
  simpa only [← _root_.norm_pow] using (GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ V) C hC hcov' μ
    inferInstance 𝓕 hμ.2 (fun g => u g ^ 2) (hu.pow 2) fun γ hγ g => by rw [hinv γ hγ]).norm

end GlobalTheory.DefiniteSqInt
