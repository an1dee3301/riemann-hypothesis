module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviComm

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem row_mul {g : Matrix (Fin n) (Fin n) R} (hF : PFr s Jm Xm Ym) (hg : cT s g * Jm * g = Jm) {d d' : Fin r → R}
    (hX : g * Xm = Xm * diagonal d) (hY : g * Ym = Ym * diagonal d') :
    cT s Ym * Jm * g = diagonal d * (cT s Ym * Jm) := by
  have h1 : cT s (diagonal d') * diagonal d = 1 := by
    have e := pgram_unitary hg Ym Xm
    rw [hY, hX, hF.yx, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * diagonal d
        = cT s (diagonal d') * (cT s Ym * Jm * Xm) * diagonal d := by rw [hF.yx, Matrix.mul_one]
      _ = 1 := by rw [← e]; simp only [Matrix.mul_assoc]
  have h2 : diagonal d * cT s (diagonal d') = 1 := mul_eq_one_comm.1 h1
  have h3 : cT s (diagonal d') * (cT s Ym * Jm * g) = cT s Ym * Jm := by
    have e : cT s (g * Ym) * Jm * g = cT s Ym * Jm := by
      conv_rhs => rw [← hg]
      simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    rw [hY, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * (cT s Ym * Jm * g) = cT s (diagonal d') * cT s Ym * Jm * g := by
          simp only [Matrix.mul_assoc]
      _ = cT s Ym * Jm := e
  calc cT s Ym * Jm * g = diagonal d * cT s (diagonal d') * (cT s Ym * Jm * g) := by rw [h2, Matrix.one_mul]
    _ = diagonal d * (cT s Ym * Jm) := by rw [Matrix.mul_assoc, h3]

theorem comm_vecMulVec {m : ℕ} {g : Matrix (Fin n) (Fin n) R} {C : Matrix (Fin n) (Fin m) R}
    {A : Matrix (Fin m) (Fin n) R} {d : Fin m → R} (hC : g * C = C * diagonal d) (hA : A * g = diagonal d * A)
    (i : Fin m) : g * vecMulVec (fun k => C k i) (A i) = vecMulVec (fun k => C k i) (A i) * g := by
  ext a b
  have e1 : ∑ k, g a k * C k i = C a i * d i := by
    have := congrFun (congrFun hC a) i
    rwa [Matrix.mul_apply, Matrix.mul_diagonal] at this
  have e2 : ∑ k, A i k * g k b = d i * A i b := by
    have := congrFun (congrFun hA i) b
    rwa [Matrix.mul_apply, Matrix.diagonal_mul] at this
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc ∑ k, g a k * (C k i * A i b) = (∑ k, g a k * C k i) * A i b := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = C a i * (d i * A i b) := by rw [e1, mul_assoc]
    _ = C a i * ∑ k, A i k * g k b := by rw [e2]
    _ = ∑ k, C a i * A i k * g k b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem lineProj_map (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
      vecMulVec (fun k => adMat F C k i)
        (((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) i) := by
  have e : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) =
      (cT (σ : E →+* E) D * J).map (inclR (F := F) (AF F)) := by
    unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul]
  rw [e]
  ext a b
  exact map_mul (inclR (F := F) (AF F)) (C a i) ((cT (σ : E →+* E) D * J) i b)

theorem leviMin_comm_projFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m) (hm : m ∈ leviMin σ J X Y) (k) :
    (matHom _ σ J m).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) =
      (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J m).1 := by
  obtain ⟨d, d', hX, hY⟩ := hm
  have hF := pfrA h hJ hW
  have hg := unitaryA_matHom m
  rcases k with i | i
  · simp only [projFam, Sum.elim_inl]
    rw [lineProj_map]
    exact comm_vecMulVec hX (row_mul hF hg hX hY) i
  · simp only [projFam, Sum.elim_inr]
    rw [lineProj_map]
    exact comm_vecMulVec hY (row_mul (pfr_swap hF) hg hY hX) i

end GlobalTheory.CompanionTheory.ParCocompact.LeviComm

end
