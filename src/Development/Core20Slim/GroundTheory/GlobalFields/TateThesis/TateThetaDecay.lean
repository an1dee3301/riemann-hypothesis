module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TateTheta
public import Batteries.Classes.RatCast
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.GroupWithZero.Prod
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem coe_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    ((moduleSection w t : IdeleGroup K) : 𝔸[K]) = (infiniteAdeleSingle w (posRealElem w t), 1) :=
  coe_infiniteEmbedding w _


theorem norm_moduleSection_apply (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) (v : InfinitePlace K) :
    ‖((moduleSection w t : IdeleGroup K) : 𝔸[K]).1 v‖ = if v = w then ‖posRealElem w t‖ else 1 := by
  rw [coe_moduleSection]
  change ‖infiniteAdeleSingle w (posRealElem w t) v‖ = _
  rw [infiniteAdeleSingle_apply]
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, norm_one]

theorem infiniteModule_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    infiniteModule (moduleSection w t) = t := by
  rw [infiniteModule, Finset.prod_eq_single w (fun v _ hv ↦ by
    rw [norm_moduleSection_apply, if_neg hv, one_pow]) (fun h ↦ absurd (Finset.mem_univ w) h),
    norm_moduleSection_apply, if_pos rfl]
  exact norm_posRealElem_pow w t.2.le

theorem norm_moduleSection_apply_le_one (w : InfinitePlace K) {t : {r : ℝ // 0 < r}}
    (ht : (t : ℝ) ≤ 1) (v : InfinitePlace K) :
    ‖((moduleSection w t : IdeleGroup K) : 𝔸[K]).1 v‖ ≤ 1 := by
  rw [norm_moduleSection_apply]
  split_ifs
  · have h := norm_posRealElem_pow w t.2.le
    have hm : w.mult ≠ 0 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
    have h2 : ‖posRealElem w t‖ ^ w.mult ≤ 1 := by rw [h]; exact ht
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm).1 h2
  · exact le_rfl

theorem normAtPlace_le_norm' (v : InfinitePlace K) (z : mixedSpace K) : normAtPlace v z ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun v ↦ normAtPlace v z) (Finset.mem_univ v)

theorem mixedEmbedding_norm_le_norm_pow (z : mixedSpace K) :
    mixedEmbedding.norm z ≤ ‖z‖ ^ Module.finrank ℚ K := by
  rw [mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (normAtPlace_nonneg _ _) _)
    fun v _ ↦ pow_le_pow_left₀ (normAtPlace_nonneg _ _) (normAtPlace_le_norm' v z) _

theorem norm_mul_le_of_normAtPlace_le_one {e : mixedSpace K} (he : ∀ v, normAtPlace v e ≤ 1)
    (z : mixedSpace K) : ‖e * z‖ ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace (e * z)]
  refine Finset.sup'_le _ _ fun v _ ↦ ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left (normAtPlace_nonneg _ _) (he v)).trans (normAtPlace_le_norm' v z)

theorem mixedEmbedding_norm_toInfinite (x : IdeleGroup K) :
    mixedEmbedding.norm (homeomorphMixedSpace K
      ((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) = infiniteModule x := by
  rw [mixedEmbedding.norm_apply]
  simp only [normAtPlace_homeomorphMixedSpace]
  rfl

theorem one_le_abs_norm_of_ne_zero {r : 𝓞 K} (hr : r ≠ 0) :
    (1 : ℝ) ≤ |((Algebra.norm ℚ (r : K) : ℚ) : ℝ)| := by
  rw [← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ r| := Int.one_le_abs h
  exact_mod_cast h1








end

end GroundTheory.Global
