module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ConductorIdeal
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.Conductor
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
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
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev HeckeCharacter : Type _ := IdeleClassGroup K →ₜ* Circle

variable {K}



namespace IdeleGroup


@[simp]
theorem toInfinite_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    toInfinite K (finiteEmbedding v a) = 1 :=
  Units.ext rfl

theorem finiteComponent_toFinite (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteComponent v (toFinite K x) = finiteProj v x :=
  Units.ext rfl

@[simp]
theorem ofFinite_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ofFinite (finiteUnitsSingle v a) = finiteEmbedding v a :=
  Units.ext rfl









end IdeleGroup

namespace HeckeCharacter

open IdeleGroup

variable (χ : HeckeCharacter K)

def toIdele : IdeleGroup K →* Circle :=
  (χ : IdeleClassGroup K →* Circle).comp (IdeleClassGroup.mk K)

theorem toIdele_apply (x : IdeleGroup K) : χ.toIdele x = χ (IdeleClassGroup.mk K x) :=
  rfl

theorem continuous_toIdele : Continuous χ.toIdele :=
  χ.continuous.comp (IdeleClassGroup.continuous_mk K)

@[simp]
theorem toIdele_diagonal (a : Kˣ) : χ.toIdele (diagonal K a) = 1 := by
  rw [toIdele_apply, IdeleClassGroup.mk_diagonal, map_one]



def infiniteComponent (w : InfinitePlace K) : (w.Completion)ˣ →ₜ* Circle where
  toMonoidHom := χ.toIdele.comp (infiniteEmbedding w)
  continuous_toFun := χ.continuous_toIdele.comp (continuous_infiniteEmbedding w)













end HeckeCharacter

end

end GroundTheory.Global
