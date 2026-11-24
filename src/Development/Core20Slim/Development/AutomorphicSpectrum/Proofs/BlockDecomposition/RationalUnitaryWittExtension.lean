module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

theorem hE_mulVec_self {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J M : Matrix (Fin n) (Fin n) E) (hM : cT (σ : E →+* E) M * J * M = J) (w : Fin n → E) :
    hE σ J (M *ᵥ w) (M *ᵥ w) = hE σ J w w := by
  have key : ∀ x y : Fin n → E, hE σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]
  have hs : (fun i => σ ((M *ᵥ w) i)) = (M.map (σ : E →+* E)) *ᵥ (fun i => σ (w i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) M w i
  rw [key, key, hs, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have : (M.map (σ : E →+* E))ᵀ *ᵥ ((J * M) *ᵥ w) = J *ᵥ w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have h := hM
    unfold cT at h
    rw [h]
  rw [this]

theorem exists_sends_hE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  intro F E _ _ _ _ _ σ _ n J _ γ hγ w
  obtain ⟨M, hM, e⟩ := hγ
  refine ⟨(M : Matrix (Fin n) (Fin n) E) *ᵥ w, ?_, hE_mulVec_self σ J _ hM w⟩
  have e' : (matHom _ σ J γ).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    have := congrArg (fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) e
    exact this.symm
  unfold Sends
  rw [e']
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (M : Matrix (Fin n) (Fin n) E) w i).symm

end GlobalTheory.CompanionTheory.RedCov

end
