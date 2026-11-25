module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilDiagIso

theorem hTens_diag_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (c : A →ₐ[R] A) (JA : Matrix (Fin (n + n)) (Fin (n + n)) A) (JB : Matrix (Fin m) (Fin m) A)
    (x y : Matrix (Fin (n + n)) (Fin m) A)
    (hx : ∀ i j, x (Fin.natAdd n i) j = x (Fin.castAdd n i) j)
    (hy : ∀ i j, y (Fin.natAdd n i) j = y (Fin.castAdd n i) j)
    (h1 : ∀ i k, JA (Fin.castAdd n i) (Fin.natAdd n k) = 0)
    (h2 : ∀ i k, JA (Fin.natAdd n i) (Fin.castAdd n k) = 0)
    (h3 : ∀ i k, JA (Fin.natAdd n i) (Fin.natAdd n k) = - JA (Fin.castAdd n i) (Fin.castAdd n k)) :
    hTens c JA JB x y = 0 := by
  unfold hTens
  simp only [Fin.sum_univ_add, hx, hy, h1, h2, h3, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]

theorem symp_diag_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (u u' : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)),
    symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u') = 0 := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ u u'
  unfold symp
  rw [hTens_diag_eq_zero]
  · simp
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]

end GlobalTheory.WeilDiagIso
