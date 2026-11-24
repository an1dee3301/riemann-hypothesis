module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoordPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCoordinatesHomeomorph
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.Tactics
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
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
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem eq_of_test_haar {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {κ P : Measure V} {χ : V → V → ℂ}
    (hκ : SelfDual κ χ) (hP : P.IsAddHaarMeasure) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂P) P) (z : V)
    (h1 : ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P = Φ (-z)) (hz : Φ (-z) ≠ 0) : κ = P := by
  have := hκ.1
  have e : κ = Measure.addHaarScalarFactor κ P • P := Measure.isAddLeftInvariant_eq_smul κ P
  set c : NNReal := Measure.addHaarScalarFactor κ P with hcdef
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂κ = (c : ℂ) * ∫ x, Φ x * χ x y ∂P := by
    intro y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hI' : Integrable (fun y => ∫ x, Φ x * χ x y ∂κ) κ := by
    simp only [hT]
    rw [e]
    exact (hI.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hκ.2 Φ hc hs hI' z
  simp only [hT] at h2
  rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h3 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂P) * χ y z ∂P =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [h3, h1, ← mul_assoc] at h2
  have h4 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ hz (by rw [h2, one_mul])
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [e, h6, one_smul]

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD
