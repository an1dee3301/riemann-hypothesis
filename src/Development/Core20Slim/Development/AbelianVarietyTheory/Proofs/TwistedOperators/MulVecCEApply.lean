module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Gen

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {κ : Type} [Fintype κ] [DecidableEq κ]

def mulVecCE (M : Matrix κ κ S) (hM : IsUnit M.det) : (κ → S) ≃ₜ+ (κ → S) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by simp [mulVec_mulVec, nonsing_inv_mul M hM]
  right_inv x := by simp [mulVec_mulVec, mul_nonsing_inv M hM]
  map_add' x y := mulVec_add M x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem mulVecCE_apply (M : Matrix κ κ S) (hM : IsUnit M.det) (x : κ → S) : mulVecCE M hM x = M *ᵥ x := rfl

end Gen

def prodCE {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) : (G₁ × G₂) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodCongr e₁.toAddEquiv e₂.toAddEquiv with
    continuous_toFun := e₁.continuous.prodMap e₂.continuous
    continuous_invFun := e₁.symm.continuous.prodMap e₂.symm.continuous }

theorem prodCE_apply {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂]
    [TopologicalSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) (x : G₁ × G₂) : prodCE e₁ e₂ x = (e₁ x.1, e₂ x.2) := rfl

def lrCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) : Matrix (Fin m) (Fin n) R ≃ₜ+ Matrix (Fin m) (Fin n) R where
  toFun u := (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R)
  invFun u := ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * u * ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  left_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  right_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  map_add' u v := by rw [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem lrCE_apply {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) (u : Matrix (Fin m) (Fin n) R) :
    lrCE g a u = (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R) := rfl

def zipHom (κ X Y : Type) [AddCommGroup X] [AddCommGroup Y] : (κ → X) × (κ → Y) →+ (κ → X × Y) where
  toFun p i := (p.1 i, p.2 i)
  map_zero' := rfl
  map_add' _ _ := rfl

section Places

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SPart : Type := ∀ v : S, Fv F v.1

abbrev OPart : Type := ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, v.1.adicCompletionIntegers F


open Classical in
def jS : SPart F S × OPart F S →+* Af F where
  toFun p := ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v),
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (by simp only [dif_neg (show v ∉ S from h)]; exact (p.2 ⟨v, h⟩).2))⟩
  map_one' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 1
    split_ifs <;> rfl)
  map_mul' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ * dite (v ∈ S) _ _
    split_ifs <;> rfl)
  map_zero' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 0
    split_ifs <;> rfl)
  map_add' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ + dite (v ∈ S) _ _
    split_ifs <;> rfl)

open Classical in
theorem evalV_jS (p : SPart F S × OPart F S) (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (jS F S p) = if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v) := rfl

end Places

end GlobalTheory.ModuLR
