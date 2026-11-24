module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift


open Formalism.REAL in
theorem kMean_translate {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {n : ℕ}
    (c : Fin n → KG (M.ε τ) → ℂ) (hc : IsCoefFam c) (w : M.H τ) (i : Fin n) (k₀ : KG (M.ε τ)) :
    ∃ d : Fin n → ℂ, M.σ τ (toMK k₀) (kMean M τ (c i) w) = ∑ j, d j • kMean M τ (c j) w := by
  have hds := M.ds τ
  have : CompleteSpace (M.H τ) := hds.1
  obtain ⟨⟨-, hmul⟩, -, hcont⟩ := hds.2.2.1
  have hmem : ∀ k : KG (M.ε τ), toMK k ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun k => (k : UJ (M.ε τ)).2
  have hcK : Continuous fun k : KG (M.ε τ) => M.σ τ (toMK k) w :=
    (hcont w).comp_continuous (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)) hmem
  have hint : ∀ j, Integrable (fun k => c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j =>
    ((hc.1 j).smul hcK).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hm : ∀ k : KG (M.ε τ), M.σ τ (toMK (k₀ * k)) = (M.σ τ (toMK k₀)).comp (M.σ τ (toMK k)) :=
    fun k => hmul _ (hmem k₀) _ (hmem k)
  obtain ⟨d, hd⟩ := hc.2 k₀⁻¹ i
  refine ⟨d, ?_⟩
  unfold kMean
  calc M.σ τ (toMK k₀) (∫ k, c i k • M.σ τ (toMK k) w ∂muK (M.ε τ))
      = ∫ k, M.σ τ (toMK k₀) (c i k • M.σ τ (toMK k) w) ∂muK (M.ε τ) :=
        (ContinuousLinearMap.integral_comp_comm _ (hint i)).symm
    _ = ∫ k, (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) (k₀ * k) ∂muK (M.ε τ) := by
        congr 1
        funext k
        simp only [map_smul, inv_mul_cancel_left]
        rw [hm]
        rfl
    _ = ∫ k, c i (k₀⁻¹ * k) • M.σ τ (toMK k) w ∂muK (M.ε τ) :=
        integral_mul_left_eq_self (μ := muK (M.ε τ)) (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) k₀
    _ = ∑ j, d j • ∫ k, c j k • M.σ τ (toMK k) w ∂muK (M.ε τ) := by
        simp only [hd, Finset.sum_smul, mul_smul]
        have hs : ∀ j ∈ (Finset.univ : Finset (Fin n)),
            Integrable (fun k => d j • c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j _ => (hint j).smul (d j)
        rw [integral_finsetSum _ hs]
        simp only [integral_smul]

theorem kMean_mem_kFin_of_coefFam : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (n : ℕ) (c : Fin n → Formalism.REAL.KG (M.ε τ) → ℂ), IsCoefFam c → ∀ (w : M.H τ) (i : Fin n),
    kMean M τ (c i) w ∈ kFin M τ := by
  intro D V S M τ n c hc w i
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin
  rw [GlobalTheory.KFiniteVectors.mem_kFiniteVectors]
  refine ⟨Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k₀, rfl⟩ := hg
  have hle : Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w) ≤
      (Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)).comap
        (M.σ τ (Formalism.REAL.toMK k₀) : M.H τ →ₗ[ℂ] M.H τ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := kMean_translate M τ c hc w j k₀
    change M.σ τ (Formalism.REAL.toMK k₀) (kMean M τ (c j) w) ∈ Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)
    rw [hd]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  exact hle hx

end GlobalTheory.Chain.IoLift
