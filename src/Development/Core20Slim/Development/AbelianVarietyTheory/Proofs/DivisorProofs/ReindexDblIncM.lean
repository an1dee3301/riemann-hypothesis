module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTargetF

open GlobalTheory.WeilSchrodinger.DblTarget

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def dblG {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin (n + n)) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl J)


theorem reindex_dbl_incM {n : ℕ} {J JA : Matrix (Fin n) (Fin n) E} (hA : JA = Jᵀ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl (incM F JA)) = incM F (dblG J)ᵀ := by
  subst hA
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [dblG, incM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.transpose_apply, Matrix.map_apply] <;> simp [dbl]







end GlobalTheory.WeilSchrodinger.DblTargetF

end
