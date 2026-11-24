module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFin
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  first | exact @GlobalTheory.SchrSuppFin.support_compact | exact GlobalTheory.SchrSuppFin.support_compact | (intros; apply GlobalTheory.SchrSuppFin.support_compact <;> assumption)
