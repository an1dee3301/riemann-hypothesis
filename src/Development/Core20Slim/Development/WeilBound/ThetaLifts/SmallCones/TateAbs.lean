module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import Development.Core20Slim.CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section


namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

namespace Tate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F E) in
abbrev Φ : AE F E ≃ₐ[AF F] AdeleRing (𝓞 E) E := adeleTensorAlgEquivLeft F E

theorem cont_Φ : Continuous (Φ F E) := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).toLinearMap

theorem cont_Φ_symm : Continuous (Φ F E).symm := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := (ideleTop F E).1.1
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).symm.toLinearMap


variable (F E) in
def Ψ : (AE F E)ˣ ≃ₜ* IdeleGroup E where
  toMulEquiv := Units.mapEquiv (Φ F E).toMulEquiv
  continuous_toFun := Continuous.units_map (Φ F E).toMulEquiv.toMonoidHom cont_Φ
  continuous_invFun := Continuous.units_map (Φ F E).symm.toMulEquiv.toMonoidHom cont_Φ_symm

theorem Ψ_val (l : (AE F E)ˣ) : ((Ψ F E l : IdeleGroup E) : AdeleRing (𝓞 E) E) = Φ F E l := rfl

theorem absE_eq (l : (AE F E)ˣ) : (absE F E l : ℝ) = IdeleGroup.ideleModule E (Ψ F E l) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), IdeleGroup.ideleModule_apply, IdeleGroup.infiniteModule,
    IdeleGroup.finiteModule, coe_ideleNorm, Ψ_val, Algebra.norm_eq_of_algEquiv, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul,
    NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow]
    rfl
  · rw [show ((∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) = _ from
      NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l)]
    refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl





end Tate


end PositivityTheory.ThKCT

end
