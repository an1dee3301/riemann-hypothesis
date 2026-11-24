module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.TraceAdd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelJointReduction
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem th_half (θ : Ainf F ⊗[F] E →+* ℂ) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
  rw [← IsScalarTower.algebraMap_apply]
  have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  exact this

theorem th_trPair (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (trPair (Ainf F) S G)) = (((S.map θ * G.map θ).trace.re : ℝ) : ℂ) := by
  rw [trPair, map_mul, map_mul, th_half, trace_add σ hCM, map_add (f := _), hc]
  have e : θ (∑ a, ∑ c, S a c * G c a) = (S.map θ * G.map θ).trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, Matrix.mul_apply, map_sum, map_mul]
  rw [e, Complex.star_def, Complex.add_conj]
  push_cast
  ring

theorem tmul_one_eq (x : Ainf F) : (x ⊗ₜ[F] (1 : E)) = algebraMap (Ainf F) (Ainf F ⊗[F] E) x := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem psi_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ)) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, th_trPair σ hCM (θ i) (hP.conj i)]

theorem psi_neg_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (-trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (-(((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ))) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, map_neg, map_neg, th_trPair σ hCM (θ i) (hP.conj i)]

theorem map_isHerm (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (b : HermR (Ainf F) σ n) :
    ((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map θ).IsHermitian := by
  ext a c
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← hc]
  exact congrArg θ (b.2 a c)

theorem gramX_eq {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) :
    gramX ε x = xᴴ * Matrix.diagonal (sgn ε) * x := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, sgn]
  simp only [Finset.sum_filter, if_true, Bool.false_eq_true, if_false]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

theorem gramX_isHerm {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) : (gramX ε x).IsHermitian := by
  rw [gramX_eq, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  have hs : star (sgn ε) = sgn ε := by
    funext a
    simp only [Pi.star_apply, sgn]
    split_ifs <;> simp
  rw [hs]

end PositivityTheory.SiegelWeilFormula.GReal
