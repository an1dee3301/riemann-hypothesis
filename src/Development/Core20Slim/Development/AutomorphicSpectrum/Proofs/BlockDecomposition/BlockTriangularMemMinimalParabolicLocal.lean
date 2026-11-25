module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extH tensNU tensNU_tmul)

namespace GlobalTheory.CompanionTheory.KFin

section Step

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
  [CommRing R'] [Algebra F R'] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)

theorem tensNU_mul_inclR (u : R ⊗[F] E) (e : E) :
    tensNU j hj u * inclR (F := F) R' e = tensNU j hj (u * inclR (F := F) R e) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]
  | tmul a e' => simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem map_tensNU_mul_inclR {a b c : Type} [Fintype b] (A : Matrix a b (R ⊗[F] E)) (X : Matrix b c E) :
    A.map (tensNU j hj) * X.map (inclR (F := F) R') = (A * X.map (inclR (F := F) R)).map (tensNU j hj) := by
  ext r s
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, tensNU_mul_inclR, map_sum]

theorem inclR_mul_map_tensNU {a b c : Type} [Fintype b] (X : Matrix a b E) (A : Matrix b c (R ⊗[F] E)) :
    X.map (inclR (F := F) R') * A.map (tensNU j hj) = (X.map (inclR (F := F) R) * A).map (tensNU j hj) := by
  ext r s
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, mul_comm (inclR (F := F) R' _), mul_comm (inclR (F := F) R _),
    tensNU_mul_inclR, map_sum]

theorem mat_extH_eq_add (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J) :
    (HA.mat R' σ J (extH σ J j hj g)).1 = 1 + ((HA.mat R σ J g).1 - 1).map (tensNU j hj) := by
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH]
  by_cases h : r = s
  · subst h
    simp [map_sub]
    ring
  · simp [Matrix.one_apply, h]

theorem extH_stab (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J)
    (X : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (hB : B.BlockTriangular id)
    (h : (HA.mat R σ J g).1 * X.map (inclR (F := F) R) = X.map (inclR (F := F) R) * B) :
    ∃ B' : Matrix (Fin r) (Fin r) (R' ⊗[F] E), B'.BlockTriangular id ∧
      (HA.mat R' σ J (extH σ J j hj g)).1 * X.map (inclR (F := F) R') = X.map (inclR (F := F) R') * B' := by
  refine ⟨1 + (B - 1).map (tensNU j hj), ?_, ?_⟩
  · intro a b hab
    have hne : a ≠ b := fun e => by subst e; exact lt_irrefl _ hab
    have h0 : B a b = 0 := hB hab
    simp [Matrix.one_apply, hne, h0]
  · rw [mat_extH_eq_add, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, map_tensNU_mul_inclR,
      inclR_mul_map_tensNU, Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]

end Step

theorem emb_mem_minPar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E))
    (hB : B.BlockTriangular id)
    (h : (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B) :
    emb σ J v p ∈ minPar σ J X := by
  obtain ⟨B₁, hB₁, h₁⟩ := extH_stab (singleFin v) (singleFin_mul v) σ J p X B hB h
  obtain ⟨B₂, hB₂, h₂⟩ := extH_stab (R' := AF F) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl) σ J _ X B₁ hB₁ h₁
  exact ⟨B₂, hB₂, h₂⟩

end GlobalTheory.CompanionTheory.KFin

end
