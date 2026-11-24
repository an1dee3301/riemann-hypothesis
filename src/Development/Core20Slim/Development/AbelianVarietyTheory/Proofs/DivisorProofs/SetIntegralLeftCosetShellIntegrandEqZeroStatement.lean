module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeftCosetShellIntegrandEqZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_leftCoset_shellIntegrand_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ) (M : ℤ), IsPeriodic ϖ M φ →
    ∀ (n : Fin a → ℤ) (i : Fin a), M ≤ n i → ∀ u : kˣ, valuation k (u : k) = 1 → ν u ≠ 1 →
    ∀ x ∈ KO k (Fin a), ∀ z : ℂ,
      ∫ g in {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)},
        φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  first | exact @GlobalTheory.ShellPiece.setIntegral_coset_eq_zero | exact GlobalTheory.ShellPiece.setIntegral_coset_eq_zero | (intros; apply GlobalTheory.ShellPiece.setIntegral_coset_eq_zero <;> assumption)
