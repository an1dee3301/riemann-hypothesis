module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TraceFourier
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace

namespace GroundTheory.Global

noncomputable section



variable {K : Type*} [Field K] [NumberField K]


namespace HeckeCharacter

variable (χ : HeckeCharacter K)






theorem toIdele_ofInfinite (a : (InfiniteAdeleRing K)ˣ) :
    χ.toIdele (IdeleGroup.ofInfinite a) =
      ∏ w, χ.infiniteComponent w (IdeleGroup.infiniteComponent w a) := by
  have ha : a = ∏ w, Units.map (IdeleGroup.infiniteAdeleSingle w) (IdeleGroup.infiniteComponent w a) := by
    ext1
    rw [Units.coe_prod]
    simp only [Units.coe_map, IdeleGroup.coe_infiniteComponent]
    exact (Finset.univ_prod_mulSingle (fun w ↦ (a : InfiniteAdeleRing K) w)).symm
  conv_lhs => rw [ha]
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ ↦ by
    rw [IdeleGroup.ofInfinite_map_infiniteAdeleSingle]
    rfl


end HeckeCharacter

end

end GroundTheory.Global
