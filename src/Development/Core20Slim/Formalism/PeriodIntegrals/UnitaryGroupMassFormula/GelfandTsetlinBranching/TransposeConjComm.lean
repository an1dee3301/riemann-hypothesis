module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.AevalScaleMonomial
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFRowActRight
public import Formalism.RealPlaceAnalysis.FockPairGl
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem transpose_conj_comm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    M.transpose.conjTranspose = M.conjTranspose.transpose := by
  ext i j; simp

theorem gram_of {n k : ℕ} {f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ} (κ : Fin n → ℕ) (hκ : Antitone κ)
    (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (g g' : Matrix (Fin n) (Fin n) ℂ) :
    fockF (rowAct ℂ (iotaC ℂ n k g).transpose f) (rowAct ℂ (iotaC ℂ n k g').transpose f) =
      fockF f f * hwAt κ (g'.conjTranspose * g) := by
  have e1 : (iotaC ℂ n k g).transpose * (iotaC ℂ n k g').transpose.conjTranspose =
      (iotaC ℂ n k (g'.conjTranspose * g)).transpose := by
    rw [iotaC_mul, iotaC_conj, Matrix.transpose_mul, transpose_conj_comm]
  rw [fockF_rowAct_right, rowAct_comp_apply, e1]
  exact mc_hw κ hκ hU hT _

theorem eval_lpMinor_top {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℕ) (h1 h2 : s ≤ n) (hs : s = n) :
    eval (fun v : Fin n × Fin n => Z v.1 v.2) (lpMinor ℂ s h1 h2) = Z.det := by
  subst hs
  rw [lpMinor, RingHom.map_det]
  congr 1
  ext p q
  simp

theorem hwAt_shift {n : ℕ} (κ' : Fin n → ℕ) (d : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hwAt (fun i => κ' i + d) Z = Z.det ^ d * hwAt κ' Z := by
  cases n with
  | zero => simp [hwAt, hw, Matrix.det_isEmpty]
  | succ m =>
    unfold hwAt hw
    simp only [map_prod, map_pow]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have hlast : ∀ ν : Fin (m + 1) → ℕ, nuNext ν (Fin.last m) = 0 := by intro ν; simp [nuNext]
    have hmid : ∀ i : Fin m, (κ' i.castSucc + d) - nuNext (fun i => κ' i + d) i.castSucc =
        κ' i.castSucc - nuNext κ' i.castSucc := by
      intro i
      have := i.isLt
      simp only [nuNext, Fin.coe_castSucc]
      split_ifs <;> omega
    simp only [hlast, hmid, Nat.sub_zero]
    rw [eval_lpMinor_top Z _ _ _ (by simp)]
    ring

theorem detPow_eq {N : ℕ} (g : GL (Fin N) ℂ) (c : ℤ) :
    detPow ℂ N g c = ((g : Matrix (Fin N) (Fin N) ℂ).det) ^ c := by
  simp [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

theorem sqAct_eq {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g f = ((g : Matrix (Fin N) (Fin N) ℂ).det ^ lam.detShift) •
      rowAct ℂ (g : Matrix (Fin N) (Fin N) ℂ).transpose f := by
  rw [sqAct, detPow_eq]

theorem sqAct_mulC {N : ℕ} (lam : DomWeight N) (g h : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam (g * h) f = sqAct ℂ N lam g (sqAct ℂ N lam h f) := by
  simp only [sqAct_eq, map_smul, smul_smul, Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul,
    rowAct_comp_apply, Matrix.det_mul]
  rw [mul_zpow]

theorem sqAct_oneC {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam 1 f = f := by
  simp [sqAct_eq, rowAct_one_apply]

def sqLC (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := sqAct ℂ N lam g
  map_add' x y := by simp only [sqAct, map_add (f := _), smul_add]
  map_smul' c x := by
    simp only [sqAct, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem sqLC_apply (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqLC N lam g f = sqAct ℂ N lam g f := rfl

theorem embGL_coe (n : ℕ) (g : GL (Fin n) ℂ) :
    ((PI.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      iotaC ℂ n 1 g := by
  simp [PI.embGL, PI.blkHom, iotaC]

theorem fixed_data {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ) (c : ℤ) (w : Fin n → ℤ)
    (κ : Fin n → ℕ) (hwκ : ∀ i, (κ i : ℤ) + c = w i)
    (hU0 : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) →
      (∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) →
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ c) • rowAct ℂ (iotaC ℂ n k g).transpose f = f)
    (hT0 : ∀ t : Fin n → ℂˣ, ((∏ i, (t i : ℂ)) ^ c) •
      rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f = (∏ i, (t i : ℂ) ^ w i) • f) :
    (∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f) ∧
    (∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f) := by
  refine ⟨fun u hu => ?_, fun t => ?_⟩
  · have hdet : u.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (fun i j h => hu.1 i j h)]
      simp [hu.2]
    have := hU0 (Matrix.GeneralLinearGroup.mkOfDetNeZero u (by rw [hdet]; exact one_ne_zero))
      (fun i j h => hu.1 i j h) (fun i => hu.2 i)
    simpa [hdet] using this
  · have h0 := hT0 t
    have hne : (∏ i, (t i : ℂ)) ^ c ≠ 0 := zpow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => (t i).ne_zero)
    have hw : (∏ i, (t i : ℂ) ^ w i) = (∏ i, (t i : ℂ) ^ κ i) * (∏ i, (t i : ℂ)) ^ c := by
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hwκ i, zpow_add₀ (t i).ne_zero, zpow_natCast]
    rw [hw, mul_comm, ← smul_smul] at h0
    exact smul_right_injective _ hne h0

end PI.WGB
