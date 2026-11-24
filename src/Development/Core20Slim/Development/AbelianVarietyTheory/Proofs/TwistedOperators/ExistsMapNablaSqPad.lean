module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open scoped Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def dropCols (r m : ℕ) : MvPolynomial (Fin r × Fin r) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
  aeval fun v => if h : v.2.val < m then X (v.1, ⟨v.2.val, h⟩) else 0

theorem dropCols_rowAct (r m : ℕ) (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    dropCols r m (rowAct ℂ g f) = rowAct ℂ g (dropCols r m f) := by
  have : (dropCols r m).comp (rowAct ℂ g) = (rowAct ℂ g).comp (dropCols r m) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hs : s.val < m <;> simp [dropCols, rowAct, hs]
  exact DFunLike.congr_fun this f

theorem dropCols_lpMinor (r m s : ℕ) (hr : s ≤ r) (hm : s ≤ m) :
    dropCols r m (lpMinor ℂ s hr hr) = lpMinor ℂ s hr hm := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext1 p q
  have hq : q.val < m := lt_of_lt_of_le q.2 hm
  simp [dropCols, hq, Fin.castLE]

theorem dropCols_hw (r m : ℕ) (h : m ≤ r) (ν : Fin m → ℕ) :
    dropCols r m (hw ℂ (le_refl r) (rowNu ν)) = hw ℂ h ν := by
  unfold hw
  rw [map_prod]
  symm
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < m := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    simp [rowNu, hs']
  · intro s _
    rw [map_pow]
    have e : nuNext (rowNu (r := r) ν) (Fin.castLE h s) = nuNext ν s := by
      simp only [nuNext, rowNu, Fin.val_castLE]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · omega
      · rfl
    have e' : rowNu (r := r) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    rw [e, e']
    congr 1
    exact (dropCols_lpMinor r m (s.val + 1) _ _).symm

theorem pad_detShift_nonneg {m : ℕ} (r : ℕ) (a : Part m) : 0 ≤ (pad r a).detShift := by
  unfold DomWeight.detShift
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

theorem pad_natW_add {m : ℕ} (r : ℕ) (a : Part m) (i : Fin r) :
    (pad r a).natW i + (pad r a).detShift.toNat = rowNu a.1 i := by
  have h0 := pad_detShift_nonneg r a
  have h1 : (pad r a).detShift ≤ (pad r a).w i := by
    unfold DomWeight.detShift
    rw [dite_eq_left i.pos]
    apply (pad r a).anti
    rw [Fin.le_def]
    have := i.2
    simp only
    omega
  have h2 : (pad r a).w i = (rowNu (r := r) a.1 i : ℕ) := rfl
  simp only [DomWeight.natW]
  omega

theorem exists_map_nablaSq_pad : ∀ (r m : ℕ) (h : m ≤ r) (a : Part m), ∃ j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ, (∀ (g : GL (Fin r) ℂ) (f : nablaSq ℂ r (pad r a)), j (sqRep ℂ r (pad r a) g f) = rowAct ℂ (g : Matrix (Fin r) (Fin r) ℂ)ᵀ (j f)) ∧ ∀ f : nablaSq ℂ r (pad r a), (f : MvPolynomial (Fin r × Fin r) ℂ) = extremal ℂ r (pad r a) → j f = hw ℂ h a.1 := by
  intro r m h a
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (pad_detShift_nonneg r a)
  let j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
    (dropCols r m).toLinearMap ∘ₗ LinearMap.mulLeft ℂ (lpMinor ℂ r le_rfl le_rfl ^ c) ∘ₗ
      (nablaSq ℂ r (pad r a)).subtype
  have hj : ∀ f, j f = dropCols r m (lpMinor ℂ r le_rfl le_rfl ^ c * f) := fun _ => rfl
  refine ⟨j, fun g f => ?_, fun f hf => ?_⟩
  · rw [hj, hj, ← dropCols_rowAct, (genericDet_pow_mul r c (fun _ => 0)).2.1, sqRep_coe, sqAct, hc,
      mul_smul_comm, Matrix.det_transpose]
    simp [detPow]
  · rw [hj, hf, extremal, genericDet_pow_mul_hw, ← dropCols_hw r m h]
    congr 2
    funext i
    have := pad_natW_add r a i
    rwa [hc, Int.toNat_natCast] at this

end GlobalTheory.GLDuality
