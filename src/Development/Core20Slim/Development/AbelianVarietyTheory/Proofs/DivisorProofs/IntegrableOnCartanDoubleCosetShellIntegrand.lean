module

public import Mathlib
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
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

namespace GlobalTheory.ShellInt

theorem integrableOn_shell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  intro k _ _ _ _ _ _ ϖ ν e hν a μ _ φ hφ n z
  have hcomp : IsCompact (shellSet ϖ n : Set (GL (Fin a) k)) :=
    (isCompact_KO.mul isCompact_singleton).mul isCompact_KO
  let χ : GL (Fin a) k →* ℂ :=
    { toFun := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z
      map_one' := by simp
      map_mul' := fun g h => by simp only [gdet_mul, map_mul, Units.val_mul, apow_mul]; ring }
  have hχ1 : ∀ g ∈ detCong (ϖ ^ e) (Fin a), χ g = 1 := by
    intro g hg
    have h1 : ν (gdet g) = 1 := hν _ hg.2
    have h2 : apow (gdet g) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1) z
    simp [χ, h1, h2]
  have hχc : Continuous χ := by
    refine continuous_of_continuousAt_one χ ?_
    have hev : (fun _ => (1 : ℂ)) =ᶠ[nhds (1 : GL (Fin a) k)] χ := by
      filter_upwards [(isOpen_detCong (ϖ ^ e) (Fin a)).mem_nhds (one_mem _)] with g hg
      exact (hχ1 g hg).symm
    have := (continuousAt_const (x := (1 : GL (Fin a) k)) (y := (1 : ℂ))).congr hev
    simpa using this
  have hcont : Continuous (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) := by
    have h := (hφ.1.continuous.comp Units.continuous_val).mul hχc
    refine h.congr fun g => ?_
    simp [χ, mul_assoc]
  exact hcont.continuousOn.integrableOn_compact hcomp

end GlobalTheory.ShellInt
