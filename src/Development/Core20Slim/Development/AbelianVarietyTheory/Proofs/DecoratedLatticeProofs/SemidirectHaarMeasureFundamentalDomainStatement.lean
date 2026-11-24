module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
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
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
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
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_haar_measure_fundamental_domain : ∀ (D : D7) (S H : HSp D) (N : Subgroup (GA D S)) (s : GA D H →* GA D S), Continuous s → IsClosed (N : Set (GA D S)) → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h') → (∀ n ∈ N, ∀ h, n * s h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ H) → ∀ (vH : Vol H) (ν : Measure N) (𝓝 : Set N), ν.IsHaarMeasure → IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν → (semiMeas N s vH.μ ν).IsHaarMeasure → ∃ 𝓡 : Set (N ⊔ s.range : Subgroup (GA D S)), IsFundamentalDomain ((GQ S ⊓ (N ⊔ s.range)).subgroupOf (N ⊔ s.range)) 𝓡 (semiMeas N s vH.μ ν) ∧ ∀ f : GA D S → ℂ, Measurable f → (IntegrableOn (fun r : (N ⊔ s.range : Subgroup (GA D S)) => f r) 𝓡 (semiMeas N s vH.μ ν) ↔ AbsConv vH.μ vH.𝓕 ν 𝓝 fun h n => f (n.1 * s h)) ∧ (AbsConv vH.μ vH.𝓕 ν 𝓝 (fun h n => f (n.1 * s h)) → ∫ r in 𝓡, f (r : GA D S) ∂(semiMeas N s vH.μ ν) = ∫ h in vH.𝓕, ∫ n in 𝓝, f (n.1 * s h) ∂ν ∂vH.μ) := by
  first | exact @GlobalTheory.Unf.semiFd_iterated | exact GlobalTheory.Unf.semiFd_iterated | (intros; apply GlobalTheory.Unf.semiFd_iterated <;> assumption)
