module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

theorem leviMat_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) :
    leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) =
      (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  let f : (A ⊗[F] E) →+* (A' ⊗[F] E) := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hf : ∀ e : E, f (inclR (F := F) A e) = inclR (F := F) A' e := fun e => by
    simp [f, inclR]
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      (Z.map (inclR (F := F) A)).map f = Z.map (inclR (F := F) A') := fun Z => by
    ext i j
    simp [hf]
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (A ⊗[F] E)) (Q : Matrix (Fin b) (Fin c) (A ⊗[F] E)),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  have hadd : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P + Q).map f = P.map f + Q.map f :=
    fun P Q => Matrix.map_add f (map_add f) P Q
  have hsub : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P - Q).map f = P.map f - Q.map f :=
    fun P Q => Matrix.map_sub f (map_sub f) P Q
  have hone : (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)).map f = 1 :=
    Matrix.map_one f (map_zero f) (map_one f)
  have hdiag : ∀ d : Fin r → A ⊗[F] E, (diagonal d).map f = diagonal (fun i => f (d i)) := fun d => by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  change leviMat σ J A' X Y (M.map f) = (leviMat σ J A X Y M).map f
  have hentry : ∀ (P : Matrix (Fin r) (Fin r) (A ⊗[F] E)) (i : Fin r), f (P i i) = (P.map f) i i :=
    fun _ _ => rfl
  simp only [leviMat, hadd, hsub, hmul, hone, hdiag, hentry, hZ]

end GlobalTheory.CompanionTheory.KFin
