module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.FiniteCoord
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Finite
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (K) in
def finiteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


variable (L) in
def finiteRestrict (v : HeightOneSpectrum (𝓞 K)) : 𝔸[L] →+* CompletionsOver L v where
  toFun y w := y.2 w.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def completionsOverBasis (v : HeightOneSpectrum (𝓞 K)) :
    Basis ι (v.adicCompletion K) (CompletionsOver L v) :=
  (Algebra.TensorProduct.basis (v.adicCompletion K) b).map (tensorEquiv L v).toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem completionsOverBasis_repr (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v)
    (i : ι) : (completionsOverBasis b v).repr z i = localCoord b v i z :=
  rfl

theorem finiteEval_norm (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    finiteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm (v.adicCompletion K) (finiteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (finiteEval K v) (finiteRestrict L v) (adeleBasis (Module.finBasis K L))
    (completionsOverBasis (Module.finBasis K L) v) (fun y i ↦ ?_) y).symm
  rw [completionsOverBasis_repr, adeleBasis_repr]
  rfl

theorem norm_adeleRing_snd (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) (y.2 w.1) :=
  (finiteEval_norm v y).trans (norm_pi _)


variable (K) in
def infiniteEval (v : InfinitePlace K) : 𝔸[K] →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


variable (L) in
def infiniteRestrict (v : InfinitePlace K) :
    𝔸[L] →+* GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v where
  toFun y w := y.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def piPlacesOverBasis (v : InfinitePlace K) :
    Basis ι v.Completion (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) :=
  (Algebra.TensorProduct.basis v.Completion b).map
    (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := L) v).toLinearEquiv

theorem piPlacesOverBasis_repr (v : InfinitePlace K)
    (z : GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) (i : ι) :
    (piPlacesOverBasis b v).repr z i = GroundTheory.Global.InfinitePlace.piPlacesOverCoord b v i z :=
  rfl

theorem infiniteEval_norm (v : InfinitePlace K) (y : 𝔸[L]) :
    infiniteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm v.Completion (infiniteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (infiniteEval K v) (infiniteRestrict L v)
    (adeleBasis (Module.finBasis K L)) (piPlacesOverBasis (Module.finBasis K L) v)
    (fun y i ↦ ?_) y).symm
  rw [piPlacesOverBasis_repr, adeleBasis_repr]
  rfl


open scoped Classical in
theorem norm_adeleRing_fst (v : InfinitePlace K) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y.1 w) :=
  by
    letI : ∀ w : v.placesOver L, Module.Finite v.Completion (w : InfinitePlace L).Completion :=
      fun w => GroundTheory.Global.InfinitePlace.finiteDimensional_completion v
        (w : InfinitePlace L)
    exact (infiniteEval_norm v y).trans (GroundTheory.Global.Algebra.norm_pi _)

end AdeleBaseChange

open AdeleBaseChange SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ideleNorm_snd (x : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) ((x : 𝔸[L]).2 w.1) :=
  norm_adeleRing_snd (K := K) v (x : 𝔸[L])


open scoped Classical in
theorem ideleNorm_fst (x : IdeleGroup L) (v : InfinitePlace K) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion ((x : 𝔸[L]).1 w) :=
  norm_adeleRing_fst (K := K) v (x : 𝔸[L])

end

end GroundTheory.Global
