module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdele
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (i : ι) : PiPlacesOver (L := L) v →ₗ[v.Completion] v.Completion :=
  ((Algebra.TensorProduct.basis v.Completion b).coord i).comp
    (tensorPiEquiv (L := L) v).symm.toLinearMap

theorem continuous_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (v : InfinitePlace K) (i : ι) :
    Continuous (piPlacesOverCoord b v i) :=
  LinearMap.continuous_of_finiteDimensional _

theorem sum_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (y : PiPlacesOver (L := L) v) (w : v.placesOver L) :
    ∑ i, algebraMap v.Completion _ (piPlacesOverCoord b v i y) *
      (b i : (w : InfinitePlace L).Completion) = y w := by
  have h := (Algebra.TensorProduct.basis v.Completion b).sum_repr
    ((tensorPiEquiv (L := L) v).symm y)
  have h2 := congrArg (fun z => tensorPiEquiv (L := L) v z w) h
  simp only [AlgEquiv.apply_symm_apply] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h2, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, Pi.smul_apply, tensorPiEquiv_apply,
    tensorPiHom_tmul, map_one, one_mul, Algebra.smul_def]
  rfl

def adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (i : ι)
    (y : InfiniteAdeleRing L) : InfiniteAdeleRing K :=
  fun v => piPlacesOverCoord b v i (fun w => y w)

theorem continuous_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (i : ι) : Continuous (adeleCoord b i) :=
  continuous_pi fun v => (continuous_piPlacesOverCoord b v i).comp
    (continuous_pi fun w => continuous_apply (w : InfinitePlace L))

theorem tensorInfiniteAdeleRingEquiv_sum_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (y : InfiniteAdeleRing L) :
    tensorInfiniteAdeleRingEquiv (∑ i, b i ⊗ₜ[K] adeleCoord b i y) = y := by
  funext w
  have ev : ∀ f : ι → InfiniteAdeleRing L, (∑ i, f i) w = ∑ i, f i w := fun f =>
    map_sum (Pi.evalAddMonoidHom (fun w : InfinitePlace L => w.Completion) w) f Finset.univ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ev]
  simp_rw [tensorInfiniteAdeleRingEquiv_tmul]
  have := sum_piPlacesOverCoord b (w.comap (algebraMap K L)) (fun w' => y w') ⟨w, liesOver_comap w⟩
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

def tmulLeft (l : L) : InfiniteAdeleRing K →ₗ[InfiniteAdeleRing K] L ⊗[K] InfiniteAdeleRing K where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def tensorInfiniteAdeleRingHomeomorph :
    letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
    L ⊗[K] InfiniteAdeleRing K ≃ₜ InfiniteAdeleRing L :=
  letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  haveI : IsModuleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  let b := Module.finBasis K L
  { toEquiv := (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).toEquiv
    continuous_toFun := by
      let φ : L ⊗[K] InfiniteAdeleRing K →ₛₗ[infiniteAdeleRingMap (K := K) (L := L)]
          InfiniteAdeleRing L :=
        { toFun := tensorInfiniteAdeleRingEquiv
          map_add' := map_add _
          map_smul' := fun c t => by
            change tensorInfiniteAdeleRingEquiv ((1 ⊗ₜ c) * t) = infiniteAdeleRingMap c * _
            rw [map_mul, tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul] }
      exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_infiniteAdeleRingMap φ
    continuous_invFun := by
      have h : ∀ y, (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y =
          ∑ i, tmulLeft (b i) (adeleCoord b i y) := fun y => by
        rw [AlgEquiv.symm_apply_eq]
        exact (tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y).symm
      change Continuous fun y => (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ =>
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (b i))).comp
          (continuous_adeleCoord b i) }

end InfinitePlace

end GroundTheory.Global
