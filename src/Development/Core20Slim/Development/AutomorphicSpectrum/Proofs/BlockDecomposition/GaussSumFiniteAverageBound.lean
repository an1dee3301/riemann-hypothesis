module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound

theorem twisted_integral_finite_coset_combination_bound :
    ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) → ∀ K : ℝ,
    (∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤ K) →
    ∀ (Q : X → ℂ) (s : Finset X),
    (∀ x, Q x = ∑ a ∈ s, Q a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x) →
    ‖∫ x, Q x * q x ∂m‖ ≤ (∑ a ∈ s, ‖Q a‖) * √K := by
  intro X _ _ _ _ _ _ _ m _ L hc ho q hq hn K hK Q s hQ
  have hopen : ∀ a : X, IsOpen {y : X | y - a ∈ L} := fun a =>
    ho.preimage (continuous_id.sub continuous_const)
  have hmeas : ∀ a : X, MeasurableSet {y : X | y - a ∈ L} := fun a => (hopen a).measurableSet
  have hcomp : ∀ a : X, IsCompact {y : X | y - a ∈ L} := by
    intro a
    have himg : {y : X | y - a ∈ L} = (fun x => x + a) '' (L : Set X) := by
      ext y
      constructor
      · intro hy
        exact ⟨y - a, hy, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [himg]
    exact hc.image (continuous_id.add continuous_const)
  have hion : ∀ a : X, IntegrableOn q {y : X | y - a ∈ L} m := fun a =>
    hq.continuousOn.integrableOn_compact (hcomp a)
  have hterm : ∀ a : X, (fun x => Set.indicator {y : X | y - a ∈ L} (fun _ => (1 : ℂ)) x * q x)
      = Set.indicator {y : X | y - a ∈ L} q := by
    intro a
    funext x
    by_cases hx : x ∈ {y : X | y - a ∈ L}
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hint : ∀ a : X, Integrable (Set.indicator {y : X | y - a ∈ L} q) m := fun a =>
    (integrable_indicator_iff (hmeas a)).2 (hion a)
  have hfun : (fun x => Q x * q x)
      = fun x => ∑ a ∈ s, Q a * Set.indicator {y : X | y - a ∈ L} q x := by
    funext x
    conv_lhs => rw [hQ x]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, congrFun (hterm a) x]
  have hsum : ∫ x, Q x * q x ∂m = ∑ a ∈ s, Q a * ∫ x in {y : X | y - a ∈ L}, q x ∂m := by
    rw [hfun, integral_finsetSum s (fun a _ => (hint a).const_mul (Q a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, integral_indicator (hmeas a)]
  have hone : ∀ a : X, ‖∫ x in {y : X | y - a ∈ L}, q x ∂m‖ ≤ √K := by
    intro a
    have h := Real.abs_le_sqrt (hK a)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hone a) (norm_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound
