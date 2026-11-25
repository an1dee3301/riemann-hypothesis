module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReTraceEq
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlanchLoc
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform

namespace PositivityTheory.Rg.Sw.Glob.PlanchH

open PositivityTheory.Rg.Sw.Glob.FTD

variable {m n : ℕ}

theorem haar_linR (A : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n) : ∃ c : ℝ, 0 < c ∧ ∀ F : V m n → ℝ, Continuous F →
    ∫ y : Fin m → Fin n → ℂ, F (A y) = c * ∫ w, F w := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set μ' : Measure (V m n) := (volume : Measure (Fin m → Fin n → ℂ)).map A with hμ'
  have : μ'.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul μ' volume
  refine ⟨Measure.addHaarScalarFactor μ' volume, by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume, fun F hF => ?_⟩
  have h' : ∫ y, F y ∂μ' = ∫ y, F y ∂(Measure.addHaarScalarFactor μ' volume • volume) :=
    congrArg (fun ν => ∫ y, F y ∂ν) h
  rw [← integral_map A.continuous.aemeasurable hF.aestronglyMeasurable, ← hμ', h', integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

end PositivityTheory.Rg.Sw.Glob.PlanchH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.FTD PositivityTheory.Rg.Sw.Glob.PlanchH

theorem planchLoc : PlanchLoc := by
  intro m n ε t ht
  obtain ⟨c1, hc1, hft⟩ := ftLoc_eq (m := m) (n := n) ε t ht
  obtain ⟨kM, hkM, hM⟩ := haar_linR (Mt (m := m) (n := n) ε t ht)
  obtain ⟨kL, hkL, hL⟩ := haar_linR (Lc (m := m) (n := n))
  refine ⟨c1 ^ 2 * kM / kL, by positivity, fun f hf => ?_⟩
  obtain ⟨S, rfl⟩ := hf
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S with hg
  have e1 : ∀ u, ‖ftLoc ε t (⇑S) u‖ ^ 2 = c1 ^ 2 * ‖(𝓕 g) (Mt ε t ht u)‖ ^ 2 := by
    intro u
    rw [hft S u, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hc1.le]
  have e2 : ∀ u, ‖S u‖ ^ 2 = ‖g (Lc u)‖ ^ 2 := by
    intro u
    simp [hg]
  simp_rw [e1, e2]
  have h1 := hM (fun w => ‖(𝓕 g) w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  have h2 := hL (fun w => ‖g w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  rw [integral_const_mul, h1, h2, SchwartzMap.integral_norm_sq_fourier g]
  field_simp

end PositivityTheory.Rg.Sw.Glob
