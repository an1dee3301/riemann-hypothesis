module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.RealPlaceAnalysis.FockPairGl
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) :
    MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin k) ℂ :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ))

theorem pairLmul_rowAct {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (h : Matrix (Fin n') (Fin n') ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : pairLmul x (rowAct ℂ h f) = pairLmul (h * x) f := by
  have : (pairLmul x).comp (rowAct ℂ (n := k) h) = pairLmul (h * x) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem rowAct_pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : rowAct ℂ g (pairLmul x f) = pairLmul (x * g) f := by
  have : (rowAct ℂ (n := k) g).comp (pairLmul x) = pairLmul (x * g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem pair_map_conj_rowAct {n k : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin k) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ g p) = rowAct ℂ (gᵀ)ᴴ (map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rowAct, map_sum]

theorem pair_map_conj_hw {n k : ℕ} (hn : k ≤ n) (ν : Fin k → ℕ) :
    map (starRingEnd ℂ) (hw ℂ hn ν) = hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext p q : 1
  simp

theorem pairLmul_hw {n n' k : ℕ} (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ) :
    pairLmul (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0) (hw ℂ hn' ν) =
      hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext p q : 1
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, pairLmul, aeval_X]
  rw [Finset.sum_eq_single (Fin.castLE (by have := s.2; omega) p)]
  · simp
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro e
      exact hb (Fin.ext (by simpa using e.symm))
  · simp

theorem pairing_equivariant_and_ne_zero : ∀ (n n' k : ℕ) (T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ), (∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f))) → (∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ), T (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ φ) (rowAct ℂ (h : Matrix (Fin n') (Fin n') ℂ)ᵀ f) = matRep n n' (g, h) (T φ f)) ∧ ∀ (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ), T (hw ℂ hn ν) (hw ℂ hn' ν) ≠ 0 := by
  intro n n' k T hT
  have hT' : ∀ φ f (x : Matrix (Fin n') (Fin n) ℂ),
      eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (pairLmul x f)) := hT
  refine ⟨fun g h φ f => ?_, fun hn hn' ν h0 => ?_⟩
  · apply MvPolynomial.funext
    intro p
    have hp : p = fun v => (Matrix.of fun a t => p (a, t)) v.1 v.2 := rfl
    rw [hp, eval_matRep, hT', hT', fockRowAdj, pairLmul_rowAct, ← pair_map_conj_rowAct, rowAct_pairLmul]
  · have h1 := hT' (hw ℂ hn ν) (hw ℂ hn' ν)
      (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0)
    rw [h0, map_zero, pairLmul_hw hn hn', pair_map_conj_hw] at h1
    have h2 := (fockPos _ _ (hwNe ℂ n k hn ν)).1
    rw [← h1] at h2
    simp at h2

end GlobalTheory.GLDuality
