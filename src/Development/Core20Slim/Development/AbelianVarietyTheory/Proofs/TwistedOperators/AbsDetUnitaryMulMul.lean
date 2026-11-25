module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open Kronecker in
theorem abs_det_unitary_mul_mul : ∀ (p q : ℕ), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∀ T : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ), (∀ B, Matrix.of (T B) = U * Matrix.of B * V) → |LinearMap.det T| = 1 := by
  classical
  intro p q U hU V hV T hT

  let e : (Fin p → Fin q → ℂ) ≃ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    { toFun := fun B j i => B i j
      invFun := fun C i j => C j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

  let L : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    LinearMap.pi (fun j => (Matrix.toLin' U).comp (LinearMap.proj j))

  let R : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    LinearMap.pi (fun i => (Matrix.toLin' Vᵀ).comp (LinearMap.proj i))
  let C : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    ((e.symm : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)) ∘ₗ L ∘ₗ
      (e.symm.symm : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ))) ∘ₗ R
  have hTC : T = C.restrictScalars ℝ := by
    apply LinearMap.ext
    intro B
    funext i j
    have h := congrFun (congrFun (hT B) i) j
    simp only [Matrix.of_apply] at h
    rw [h, Matrix.mul_assoc]
    simp [C, L, R, e, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hL : LinearMap.det L = U.det ^ q := by
    simp [L, LinearMap.det_pi, LinearMap.det_toLin']
  have hR : LinearMap.det R = V.det ^ p := by
    simp [R, LinearMap.det_pi, LinearMap.det_toLin', Matrix.det_transpose]
  have hC : LinearMap.det C = U.det ^ q * V.det ^ p := by
    simp only [C]
    rw [LinearMap.det_comp, LinearMap.det_conj L e.symm, hL, hR]
  have hu : ‖U.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  have hv : ‖V.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hV)
  rw [hTC, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hC, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hu, hv]
  simp

end GlobalTheory.PolarU
