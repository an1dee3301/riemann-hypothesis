module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

theorem thetaC_neg {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (fun x ↦ F (-x)) h = thetaC F h := by
  unfold thetaC
  rw [← (Equiv.neg (ι → k)).tsum_eq (fun ξ => F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))]
  refine tsum_congr fun ξ => ?_
  have hr : ratV (-ξ) = -ratV ξ := by
    funext i
    simp [ratV]
  simp only [Equiv.neg_apply, hr, Matrix.mulVec_neg]

theorem thetaCInt_neg : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k),
    thetaCInt w (fun x ↦ F (-x)) ω = thetaCInt w F ω := by
  intro k _ _ ι _ _ w F ω
  funext t
  unfold thetaCInt
  simp only [thetaC_neg]

end GlobalTheory.CompanionTheory.AdelicThetaSeries
