module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM    

noncomputable section

namespace GlobalTheory.LeviOp

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem map_inv_mul {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A⁻¹.map g * A.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem map_mul_inv {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A.map g * A⁻¹.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem hom_mulVec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (g : F →+* S) (g' : F →+* T)
    (hg : f.comp g = g') (M : Matrix κ κ F) (x : κ → S) (i : κ) :
    f ((M.map g *ᵥ x) i) = (M.map g' *ᵥ (fun j => f (x j))) i := by
  subst hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]



def homeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S) (A : Matrix κ κ F)
    (hA : IsUnit A.det) : (κ → S) ≃ₜ (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem homeo_apply {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (x : κ → S) : homeo g A hA x = A⁻¹.map g *ᵥ x := rfl

def linEquiv {S : Type} [CommRing S] [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) : (κ → S) ≃L[ℝ] (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := Matrix.mulVec_smul _ c x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem sb_comp {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {φ : X → ℂ} (hφ : φ ∈ SB X) : φ ∘ h ∈ SB X :=
  ⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩

variable [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)





end GlobalTheory.LeviOp
