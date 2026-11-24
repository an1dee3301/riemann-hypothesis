module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PermutationWordGelfandPolynomialModShorter
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Simproc
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.GetElem
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.RingTheory.FiniteType

@[expose] public section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel  GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.GelfCyc

open GlobalTheory.SmoothForms (gelfA gelfA_eq_sum_pow)

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem gelfA_conj (G : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (k : ℕ) :
    gelfA (fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) k = gelfA G k := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix
  have hc : ∀ (M : Matrix (Fin n) (Fin n) A) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d := by
    intro M a b
    simp only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]
  have h1 : (Matrix.of fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) = φ P * Matrix.of G * φ Q := by
    ext a b
    rw [hc]
    rfl
  have h2 : ∀ m : ℕ, (φ P * Matrix.of G * φ Q) ^ m = φ P * Matrix.of G ^ m * φ Q := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]
    | succ m ih =>
      have : φ Q * φ P = 1 := by rw [← map_mul, hQP, map_one]
      rw [pow_succ, pow_succ, ih]
      simp only [mul_assoc]
      rw [← mul_assoc (φ Q), this, one_mul]
  rw [gelfA_eq_sum_pow, gelfA_eq_sum_pow, h1, h2]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have : ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of G ^ (k + 1)) c d = (Q * P) d c • (Matrix.of G ^ (k + 1)) c d := by
    intro d
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [mul_comm]
  simp [this, hQP, Matrix.one_apply]

theorem gelfA_swap (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA (fun a b => E b a) k = ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).reverse.prod := by
  rw [gelfA]
  refine (Fintype.sum_equiv ((Equiv.neg (Fin (k + 1))).arrowCongr (Equiv.refl _)) _ _ fun idx => ?_).symm
  congr 1
  have h : ∀ a : Fin (k + 1), a.rev + 1 = -a := fun a => by
    have : a.rev + a = Fin.last k := Fin.ext (by
      have := a.2
      rw [Fin.val_add, Fin.val_rev, Fin.val_last, Nat.mod_eq_of_lt] <;> omega)
    rw [eq_neg_iff_add_eq_zero, add_right_comm, this, Fin.last_add_one]
  have h' : ∀ a : Fin (k + 1), a.rev = -(a + 1) := fun a => by
    rw [neg_add, ← h, add_neg_cancel_right]
  have e : ∀ g : Fin (k + 1) → A, (List.ofFn g).reverse = List.ofFn fun a => g a.rev := fun g => by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp
  rw [e]
  congr 1
  funext a
  rw [h, h']
  rfl

theorem prod_ofFn_neg : ∀ (m : ℕ) (g : Fin m → A),
    (List.ofFn fun a => -g a).prod = (-1 : ℂ) ^ m • (List.ofFn g).prod
  | 0, _ => by simp
  | m + 1, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, prod_ofFn_neg m fun a => g a.succ, pow_succ]
    simp

theorem sum_words (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).reverse.prod := by
  have e : ∀ a b, φ (M * (Matrix.single a b 1)ᵀ * M⁻¹) = ∑ c, ∑ d, (M⁻¹ a c * M d b) • φ (Matrix.single d c 1) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    congr 1
    rw [Matrix.matrix_eq_sum_single (M * _ * _), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    simp [Matrix.mul_apply, Matrix.single, ite_and, mul_comm]
  rw [← gelfA_swap (fun a b => φ (Matrix.single a b 1)),
    ← gelfA_conj _ M⁻¹ M (Matrix.mul_nonsing_inv M hM), gelfA, Finset.smul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp only [map_neg, e]
  exact prod_ofFn_neg _ _

end Alg

open GlobalTheory.Mem.RealTranslate (derEnd)

theorem wordDer_eq {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (τ : D.what₂.Tau)
    (w : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : SmFun θ V) :
    wordDer θ V τ w f.1 = ((w.map (derEnd hθ τ)).prod f).1 := by
  induction w with
  | nil => rfl
  | cons Z w ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    show RderC θ V τ Z (wordDer θ V τ w f.1) = _
    rw [ih]
    rfl

end GlobalTheory.RegSch.GelfCyc

end
