module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.Statement
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG  GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem signs_pos_of_frame_gram_posdef {r : ℕ} (ε : Fin r → Bool) (fr G : Matrix (Fin r) (Fin r) ℂ)
    (h : fr.conjTranspose * Formalism.REAL.Jm ε * fr = G) (hs : Formalism.UG.HasSignature G r 0) :
    ∀ i, ε i = true := by
  obtain ⟨e, P, hP⟩ := hs
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ) =
      (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hJ0 : Formalism.UG.Jpq r 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  rw [hcT, hJ0] at hP
  set P' : Matrix (Fin r) (Fin r) ℂ := (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).submatrix e e with hP'
  have h1 : P'.conjTranspose * G * P' = 1 := by
    have := congrArg (fun A : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ => A.submatrix e e) hP
    simp only [Matrix.reindex_apply] at this
    rw [← Matrix.submatrix_mul_equiv _ _ _ e _, ← Matrix.submatrix_mul_equiv _ _ _ e _] at this
    simpa [Matrix.submatrix_submatrix, Matrix.conjTranspose_submatrix, hP'] using this
  set Q := fr * P' with hQ
  have h2 : (Q.conjTranspose * Formalism.REAL.Jm ε) * Q = 1 := by
    rw [← h1, ← h]; simp only [hQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 : Q * (Q.conjTranspose * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp h2
  have h4 : Q * Q.conjTranspose = Formalism.REAL.Jm ε := by
    have := congrArg (· * Formalism.REAL.Jm ε) h3
    simpa [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self] using this
  intro i
  by_contra hi
  have hi' : ε i = false := by simpa using hi
  have h5 := congrFun (congrFun h4 i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hi'] at h5
  have h6 := congrArg Complex.re h5
  simp only [Complex.re_sum, Bool.false_eq_true, if_false, Complex.neg_re, Complex.one_re] at h6
  have h7 : ∀ k, 0 ≤ (Q i k * star (Q i k)).re := by
    intro k
    rw [Complex.star_def, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => h7 k)
  linarith

end GlobalTheory
