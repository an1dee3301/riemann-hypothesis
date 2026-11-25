module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianWitt
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Logic.Function.Defs
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] {ι : Type*} [Fintype ι] [DecidableEq ι]


end Transport

section Split

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

section OfGram

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermitianForm.ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) : HermitianForm F A (ι → A) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F A) (RingHom.id A)
    (fun x y => ∑ i, ∑ j, conj F A (x i) * H i j * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  isSymm := ⟨fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : conj F A (H j i) = H i j := congrFun (congrFun hH i) j
    rw [this]
    ring⟩
  nonsingular := by
    refine bijective_of_injective_sesq _ ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hv : Matrix.vecMul (fun i => conj F A (x i)) H = 0 := by
      funext j
      have := LinearMap.congr_fun hx (Pi.single j 1)
      rw [LinearMap.mk₂'ₛₗ_apply] at this
      simpa [vecMul, dotProduct, Pi.single_apply] using this
    have hinj := (Matrix.vecMul_injective_iff_isUnit (A := H)).2
      ((Matrix.isUnit_iff_isUnit_det H).2 hu)
    have h0 := hinj (hv.trans (Matrix.zero_vecMul H).symm)
    funext i
    have := congrFun h0 i
    rw [← conj_conj (F := F) (x i), this]
    simp

theorem HermitianForm.ofGram_apply (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) (x y : ι → A) :
    (HermitianForm.ofGram H hH hu).toSesq x y = ∑ i, ∑ j, conj F A (x i) * H i j * y j :=
  rfl

theorem gram_ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) :
    gram (HermitianForm.ofGram H hH hu).toSesq (Pi.basisFun A ι) = H := by
  ext i j
  rw [gram_apply, HermitianForm.ofGram_apply]
  simp [Pi.single_apply]

end OfGram

section LocalField

variable {F A : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A] [Algebra.IsSeparable F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end LocalField

section Diagonal

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]

end Diagonal

end GroundTheory.Automorphic
