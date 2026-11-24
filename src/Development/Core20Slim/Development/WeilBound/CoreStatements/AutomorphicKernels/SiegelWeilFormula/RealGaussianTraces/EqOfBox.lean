module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.SecondCountableTens
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

open Topology in
theorem eq_of_box {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (hB : IsOpen B) (g1 g2 : X → ℂ)
    (h1 : ContinuousOn g1 B) (h2 : ContinuousOn g2 B) (t : X) (ht : t ∈ B)
    (hbox : ∀ U ∈ 𝓝 t, ∃ S, IsCompact S ∧ S ⊆ U ∧ S ⊆ B ∧ S ∈ 𝓝 t ∧ ∫ x in S, g1 x ∂ν = ∫ x in S, g2 x ∂ν) :
    g1 t = g2 t := by
  by_contra hne
  set c := g1 t - g2 t with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr hne
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hcont : ContinuousAt (fun x => g1 x - g2 x) t := (h1.sub h2).continuousAt (hB.mem_nhds ht)
  have hU : {x | ‖(g1 x - g2 x) - c‖ < ‖c‖ / 2} ∈ 𝓝 t := by
    have := hcont.eventually (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ‖c‖ / 2))
    filter_upwards [this] with x hx
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  obtain ⟨S, hSc, hSU, hSB, hSt, hint⟩ := hbox _ hU
  have hSfin : ν S < ⊤ := hSc.measure_lt_top
  have hSpos : 0 < ν S := Measure.measure_pos_of_mem_nhds (μ := ν) hSt
  have hSr : 0 < ν.real S := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hi1 : IntegrableOn g1 S ν := (h1.mono hSB).integrableOn_compact hSc
  have hi2 : IntegrableOn g2 S ν := (h2.mono hSB).integrableOn_compact hSc
  have hi12 : IntegrableOn (fun x => g1 x - g2 x) S ν := hi1.sub hi2
  have hic : IntegrableOn (fun _ : X => c) S ν := integrableOn_const hSfin.ne
  have h0 : ∫ x in S, (g1 x - g2 x - c) ∂ν = -(ν.real S • c) := by
    rw [integral_sub hi12 hic, integral_sub hi1 hi2, hint, sub_self, setIntegral_const, zero_sub]
  have hle : ‖∫ x in S, (g1 x - g2 x - c) ∂ν‖ ≤ ‖c‖ / 2 * ν.real S :=
    norm_setIntegral_le_of_norm_le_const hSfin (fun x hx => (hSU hx).le)
  rw [h0, norm_neg, norm_smul, Real.norm_of_nonneg hSr.le] at hle
  nlinarith

end PositivityTheory.SiegelWeilFormula.GReal
