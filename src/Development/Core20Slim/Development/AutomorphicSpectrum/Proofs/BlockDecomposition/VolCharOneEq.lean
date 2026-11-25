module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
public import Init.Core
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Induced

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinVol

theorem volChar_one_eq {k : Type} [Field k] [NumberField k] :
    ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ) := by
  haveI := GroundTheory.Global.isHaarMeasure_normOneMeasure k
  haveI : Countable ↥(GroundTheory.Global.diagonalNormOne k).op := by
    haveI := GroundTheory.Global.countable_diagonalNormOne k
    refine Function.Injective.countable (f := fun x : ↥(GroundTheory.Global.diagonalNormOne k).op =>
      (⟨x.1.unop, Subgroup.mem_op.mp x.2⟩ : ↥(GroundTheory.Global.diagonalNormOne k))) ?_
    intro x y h
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val h
  have hfin : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) < ⊤ :=
    GroundTheory.Global.normOneMeasure_normOneFundamentalDomain_lt_top k
  have hne : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) ≠ 0 :=
    (GroundTheory.Global.isFundamentalDomain_normOneFundamentalDomain k
      (GroundTheory.Global.normOneMeasure k)).measure_ne_zero (NeZero.ne _)
  refine ⟨(GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k)).toReal,
    ENNReal.toReal_pos hne hfin.ne, ?_⟩
  have h2 : volChar (1 : HeckeCharacter k) =
      ∫ _u in GroundTheory.Global.normOneFundamentalDomain k, (1 : ℂ) ∂GroundTheory.Global.normOneMeasure k := by
    unfold volChar
    congr 1
  rw [h2, MeasureTheory.setIntegral_const]
  simp [Measure.real]

end GlobalTheory.CompanionTheory.EpsteinVol
