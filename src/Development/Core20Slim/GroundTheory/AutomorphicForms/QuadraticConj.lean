module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Automorphic

open Module

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]

noncomputable def conjLinear : E →ₗ[F] E :=
  (Algebra.linearMap F E).comp (Algebra.trace F E) - LinearMap.id

variable {F E}

theorem conjLinear_apply (x : E) :
    conjLinear F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

variable [Algebra.IsQuadraticExtension F E]

theorem trace_algebraMap_quadratic (c : F) : Algebra.trace F E (algebraMap F E c) = 2 * c := by
  rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, nsmul_eq_mul]
  norm_num

theorem conjLinear_algebraMap (c : F) : conjLinear F E (algebraMap F E c) = algebraMap F E c := by
  rw [conjLinear_apply, trace_algebraMap_quadratic, map_mul, map_ofNat]
  ring

theorem conjLinear_one : conjLinear F E 1 = 1 := by
  simpa using conjLinear_algebraMap (F := F) (E := E) 1


omit [Algebra.IsQuadraticExtension F E] in
theorem linearIndependent_one_of_not_mem [Nontrivial E] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : LinearIndependent F ![1, x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    by_contra hs
    exact one_ne_zero ((smul_eq_zero.mp hst).resolve_left hs)
  · exfalso
    apply hx
    refine ⟨-(s / t), ?_⟩
    have : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
    rw [Algebra.algebraMap_eq_smul_one]
    have h2 : x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem nontrivial_quadratic (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsQuadraticExtension K A] : Nontrivial A :=
  Module.nontrivial_of_finrank_pos (R := K) (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; norm_num)

noncomputable def basisOneOf {x : E} (hx : x ∉ Set.range (algebraMap F E)) : Basis (Fin 2) F E :=
  haveI := nontrivial_quadratic F E
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_not_mem hx)
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two, Fintype.card_fin])

theorem basisOneOf_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 0 = 1 := by
  simp [basisOneOf]

theorem basisOneOf_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 1 = x := by
  simp [basisOneOf]

theorem sq_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    x * x = algebraMap F E ((basisOneOf hx).repr (x * x) 0) +
      algebraMap F E ((basisOneOf hx).repr (x * x) 1) * x := by
  conv_lhs => rw [← (basisOneOf hx).sum_repr (x * x)]
  rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one, Algebra.smul_def, Algebra.smul_def,
    mul_one]

theorem repr_self_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 0 = 0 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

theorem repr_self_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 1 = 1 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

theorem trace_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := by
  rw [Algebra.trace_eq_matrix_trace (basisOneOf hx), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, zero_add]

theorem norm_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.norm F x = -(basisOneOf hx).repr (x * x) 0 := by
  rw [Algebra.norm_eq_matrix_det (basisOneOf hx), Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, repr_self_one]
  ring

theorem conjLinear_mul_self (x : E) :
    conjLinear F E (x * x) = conjLinear F E x * conjLinear F E x := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [← map_mul, conjLinear_algebraMap, conjLinear_algebraMap, map_mul]
  · have hsq := sq_eq_of_not_mem hx
    have htr : Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := trace_eq_of_not_mem hx
    have htr2 : Algebra.trace F E (x * x) = 2 * (basisOneOf hx).repr (x * x) 0 +
        (basisOneOf hx).repr (x * x) 1 * (basisOneOf hx).repr (x * x) 1 := by
      conv_lhs => rw [hsq]
      rw [map_add (f := _), trace_algebraMap_quadratic, ← Algebra.smul_def, map_smul, htr, smul_eq_mul]
    rw [conjLinear_apply, conjLinear_apply, htr2, htr]
    simp only [map_add (f := _), map_mul, map_ofNat]
    linear_combination (-2 : E) * hsq

theorem conjLinear_mul (x y : E) :
    conjLinear F E (x * y) = conjLinear F E x * conjLinear F E y := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conjLinear_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  · have key : (conjLinear F E).comp (LinearMap.mulLeft F x) =
        (LinearMap.mulLeft F (conjLinear F E x)).comp (conjLinear F E) := by
      refine (basisOneOf hx).ext fun i => ?_
      fin_cases i
      · simp [basisOneOf_zero, conjLinear_one]
      · simp only [Fin.mk_one, basisOneOf_one, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mulLeft_apply]
        exact conjLinear_mul_self x
    exact LinearMap.congr_fun key y

theorem conjLinear_conjLinear (x : E) : conjLinear F E (conjLinear F E x) = x := by
  rw [conjLinear_apply, conjLinear_apply x, map_sub, trace_algebraMap_quadratic, map_sub,
    map_mul, map_ofNat]
  ring

variable (F E) in
noncomputable def conj : E ≃ₐ[F] E :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInvolutive (conjLinear F E) (fun x => conjLinear_conjLinear x))
    conjLinear_one conjLinear_mul

theorem conj_apply (x : E) : conj F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

@[simp]
theorem conj_conj (x : E) : conj F E (conj F E x) = x := conjLinear_conjLinear x

theorem conj_algebraMap (c : F) : conj F E (algebraMap F E c) = algebraMap F E c :=
  conjLinear_algebraMap c

theorem add_conj (x : E) : x + conj F E x = algebraMap F E (Algebra.trace F E x) := by
  rw [conj_apply]; ring

theorem mul_conj (x : E) : x * conj F E x = algebraMap F E (Algebra.norm F x) := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conj_algebraMap, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow, sq]
  · have hsq := sq_eq_of_not_mem hx
    rw [conj_apply, trace_eq_of_not_mem hx, norm_eq_of_not_mem hx, map_neg]
    linear_combination (-1 : E) * hsq

end GroundTheory.Automorphic
