module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Init.Core
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.PowersetCard
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.RelIso.Basic

@[expose] public section

open Matrix
open scoped Classical

namespace GlobalTheory

noncomputable def strictMonoEquivPowersetCard (a : ℕ) (n : Type*) [LinearOrder n] :
    {s : Fin a → n // StrictMono s} ≃ Set.powersetCard n a :=
  ({ toFun := fun s => OrderEmbedding.ofStrictMono s.1 s.2
     invFun := fun f => ⟨f, f.strictMono⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => by ext; rfl } : {s : Fin a → n // StrictMono s} ≃ (Fin a ↪o n)).trans
    Set.powersetCard.ofFinEmbEquiv

theorem subsetEnum_strictMonoEquivPowersetCard (a : ℕ) {n : Type*} [LinearOrder n]
    (s : {s : Fin a → n // StrictMono s}) :
    subsetEnum (strictMonoEquivPowersetCard a n s) = s.1 := by
  have h : Set.powersetCard.ofFinEmbEquiv.symm (strictMonoEquivPowersetCard a n s) =
      OrderEmbedding.ofStrictMono s.1 s.2 := Equiv.symm_apply_apply _ _
  exact congrArg (fun f : Fin a ↪o n => (f : Fin a → n)) h

theorem minorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ),
    M ∈ Matrix.unitaryGroup (Fin N) ℂ →
    (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈
      Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  intro N a M hM
  set e := strictMonoEquivPowersetCard a (Fin N)
  have hC : (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) =
      (compoundMatrix a Mᵀ).submatrix e e := by
    ext s s'
    have he : ∀ s, subsetEnum (e s) = s.1 := subsetEnum_strictMonoEquivPowersetCard a
    simp only [submatrix_apply, compoundMatrix, of_apply, he]
    rfl
  have hT : Mᵀ * (Mᵀ)ᴴ = 1 := by
    rw [mem_unitaryGroup_iff'] at hM
    have h1 : Mᵀ * (Mᵀ)ᴴ = (star M * M)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, mul_comm]
    rw [h1, hM, transpose_one]
  rw [hC, mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv, ← compoundMatrix_conjTranspose, ← compoundMatrix_mul, hT,
    compoundMatrix_one, submatrix_one_equiv]

end GlobalTheory
