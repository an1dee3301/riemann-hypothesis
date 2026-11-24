module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLintegralSqNeTop
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
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
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  first | exact @GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | exact GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | (intros; apply GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self <;> assumption)
