module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.CartanTensor

open Matrix
open scoped Kronecker ComplexOrder

variable {n d : ℕ}

theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

theorem cartan_comm {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M * θ.map star = θᵀ * M := by
  obtain ⟨h1, h2, -⟩ := h
  have h1' : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1]
    exact Matrix.map_one star (star_zero _) (star_one _)
  calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [h2]
    _ = θᵀ * M := by rw [Matrix.mul_assoc (θᵀ * M), h1', Matrix.mul_one]

theorem cartan_posDef {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) :
    (θᵀ * M).PosDef := by
  have hH : (θᵀ * M).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, ← cartan_comm h]
    congr 1 <;> ext i j <;> simp [hM]
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun c hc => Complex.pos_iff.2 ⟨?_, (hH.im_star_dotProduct_mulVec_self c).symm⟩⟩
  have hx : star c ≠ 0 := by simpa using hc
  have := h.2.2 (star c) hx
  rw [star_star] at this
  convert this using 2
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem quadruple_sum_eq_trace_transpose_mul (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * A i k * B j l * star (y k l)) = trace (xᵀ * (A * y.map star * Bᵀ)) := by
  rw [← trace_transpose_mul, transpose_transpose]
  simp only [trace, diag_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadruple_sum_eq_kronecker_quadraticForm (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) (x : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * P i k * Q j l * star (x k l)) =
      star (fun p : Fin n × Fin d => star (x p.1 p.2)) ⬝ᵥ ((P ⊗ₖ Q) *ᵥ fun p : Fin n × Fin d => star (x p.1 p.2)) := by
  simp only [dotProduct, mulVec, kronecker_apply, Fintype.sum_prod_type, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem map_star_smulI {a b : Type} (M : Matrix a b ℂ) : (Complex.I • M).map star = (-Complex.I) • M.map star := by
  ext i j; simp

theorem cancelI {A B : Matrix (Fin d) (Fin d) ℂ} (h : Complex.I • A = Complex.I • B) : A = B :=
  smul_right_injective _ Complex.I_ne_zero h

theorem tensor_cartan_invariant_pos : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  intro n d JX θX JW θW hJX hX hJW hW x y
  have hWc : θWᵀ * JW * θW.map star = JW := by
    have h := hW.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cW : JW * θW.map star = θWᵀ * JW := by
    have h := cartan_comm hW
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cX := cartan_comm hX
  have hIW : ∀ i j, star ((Complex.I • JW) j i) = (Complex.I • JW) i j := by
    intro i j; simp [hJW]
  constructor
  · rw [quadruple_sum_eq_trace_transpose_mul, quadruple_sum_eq_trace_transpose_mul]
    have e1 : (Complex.I • (θX * x * θWᵀ))ᵀ * (JX * (Complex.I • (θX * y * θWᵀ)).map star * JWᵀ) =
        θW * (xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ) := by
      rw [map_star_smulI, transpose_smul, map_star_mul, map_star_mul, transpose_mul, transpose_mul, transpose_transpose,
        transpose_map]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_mul]
    have e2 : xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ * θW =
        xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θWᵀ * JW * θW.map star)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e1, trace_mul_comm, e2, hX.2.1, hWc]
    simp only [Matrix.mul_assoc]
  · intro hx
    have e3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
        -(xᵀ * ((θXᵀ * JX) * x.map star * (θWᵀ * (Complex.I • JW))ᵀ)) := by
      have h3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
          (-Complex.I) • (xᵀ * (JX * θX.map star) * x.map star * (JW * θW.map star)ᵀ) := by
        rw [map_star_smulI, map_star_mul, map_star_mul, transpose_map, transpose_mul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      rw [h3, cX, cW]
      simp only [Matrix.smul_mul, Matrix.mul_smul, transpose_smul, neg_smul, Matrix.mul_assoc]
    rw [quadruple_sum_eq_trace_transpose_mul, e3, trace_neg, Complex.neg_re, neg_neg,
      ← quadruple_sum_eq_trace_transpose_mul (θXᵀ * JX) (θWᵀ * (Complex.I • JW)) x x, quadruple_sum_eq_kronecker_quadraticForm]
    have hK := (cartan_posDef hJX hX).kronecker (cartan_posDef hIW hW)
    have hc : (fun p : Fin n × Fin d => star (x p.1 p.2)) ≠ 0 := by
      intro h; apply hx; ext i j; have := congrFun h (i, j); simpa using this
    exact (Complex.pos_iff.1 ((posDef_iff_dotProduct_mulVec.1 hK).2 hc)).1

end GlobalTheory.CartanTensor
