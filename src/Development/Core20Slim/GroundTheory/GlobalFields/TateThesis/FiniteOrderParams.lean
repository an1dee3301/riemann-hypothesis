module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Init.Core
public import Init.Data.Cast
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
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

set_option maxSynthPendingDepth 1

open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

open IdeleGroup

variable (χ : HeckeCharacter K)

theorem exists_toIdele_pow_eq_one (h : IsOfFinOrder χ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : IdeleGroup K, χ.toIdele x ^ n = 1 := by
  obtain ⟨n, hn, hχ⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine ⟨n, hn, fun x ↦ ?_⟩
  rw [toIdele_apply, ← ContinuousMonoidHom.pow_apply, hχ]
  rfl

theorem realComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsReal) {x : ℝˣ} (hx : 0 < (x : ℝ)) : χ.realComponent hw x = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  have hr : 0 < (x : ℝ) ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos hx _
  have hy : Units.mk0 _ hr.ne' ^ n = x := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hx.le hn.ne'])
  rw [← hy, map_pow]
  exact hpow (infiniteEmbedding w (realUnitsHom hw (Units.mk0 _ hr.ne')))

theorem complexComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsComplex) (z : ℂˣ) : χ.complexComponent hw z = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact z.ne_zero hy.symm
  have hyz : Units.mk0 y hy0 ^ n = z := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])
  rw [← hyz, map_pow]
  exact hpow (infiniteEmbedding w (complexUnitsHom hw (Units.mk0 y hy0)))

end HeckeCharacter

end

end GroundTheory.Global
