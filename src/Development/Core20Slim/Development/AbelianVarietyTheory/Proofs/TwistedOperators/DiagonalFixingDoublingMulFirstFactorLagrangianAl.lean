module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelPar
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblIdent

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Matrix in
theorem fromRows_add_fromRows {R : Type} [Add R] {m₁ m₂ n : Type} (A B : Matrix m₁ n R) (C D : Matrix m₂ n R) :
    fromRows A C + fromRows B D = fromRows (A + B) (C + D) := by
  ext (i | i) j <;> rfl

open Matrix in
theorem smul_fromRows {R S : Type} [SMul S R] {m₁ m₂ n : Type} (s : S) (A : Matrix m₁ n R) (C : Matrix m₂ n R) :
    s • fromRows A C = fromRows (s • A) (s • C) := by
  ext (i | i) j <;> rfl

theorem nT_eq {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (X Y : Matrix (Fin d) (Fin d) R)
    (h2 : (Y + 1) * (X + 1) = 1) (hc : (c * c) • X = X) :
    ((h * h * h) • ((1 - c) • X - (1 + c) • Y)) * (1 + (h * (1 + c)) • X) = (h * h) • X := by
  have hYX : Y * X = -X - Y := by
    have e : Y * X + X + Y = 0 := by
      have := h2; rw [add_mul, mul_add, mul_add, mul_one, one_mul, one_mul] at this
      rw [← sub_eq_zero] at this; rw [← this]; abel
    rw [← sub_eq_zero, ← e]; abel
  have hY : (c * c) • Y = Y := by
    have e : Y = -((Y + 1) * X) := by
      rw [add_mul, one_mul, hYX]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hc]
  have hXX : (c * c) • (X * X) = X * X := by rw [← Matrix.smul_mul, hc]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul,
    smul_sub, smul_add, smul_smul, Matrix.mul_sub]
  linear_combination (norm := module) (-(h ^ 4 * (1 + c) ^ 2)) • hYX - h ^ 4 • hXX + h ^ 4 • hc + h ^ 4 • hY +
    hh • ((h ^ 3 * (1 + c) + h ^ 2) • X + (h ^ 3 * (1 + c)) • Y)

theorem blocks {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (K N T : Matrix (Fin d) (Fin d) R)
    (hT : T = 1 + (h * (1 + c)) • (K - 1)) (hNT : N * T = (h * h) • (K - 1)) :
    (1 + (h * c) • (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R))ᵀ)) *
        Matrix.fromBlocks K 0 0 (1 : Matrix (Fin d) (Fin d) R) * Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) =
      (1 + Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R) * N * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R))ᵀ) *
        Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * T := by
  simp only [Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg, Matrix.add_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_add, smul_fromRows,
    fromRows_add_fromRows, hNT]
  rw [Matrix.fromRows_inj.eq_iff]
  subst hT
  constructor
  · linear_combination (norm := module) hh • (-(h + 1) • (K - 1))
  · linear_combination (norm := module) hh • (h • (K - 1))

end GlobalTheory.SplitDblIdent

namespace GlobalTheory.SplitDblGen

theorem half_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    (half : AE F E) * 2 = 1 := by
  rw [half, show (2 : AE F E) = algebraMap (AF F) (AE F E) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem diagonalFixingDoubling_mul_firstFactor_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → K' * K = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d * Matrix.fromBlocks K 0 0 1 * diagCols (E := AE F E) (Fin d) =
      GlobalTheory.SplitDblGen.nMat c K K' * diagCols (E := AE F E) (Fin d) * GlobalTheory.SplitDblGen.tMat c K := by
  intro F E _ _ _ _ _ d c K K' _ h2 hc
  have hNT := GlobalTheory.SplitDblIdent.nT_eq half c half_mul_two (K - 1) (K' - 1) (by simpa using h2) hc
  exact GlobalTheory.SplitDblIdent.blocks half c half_mul_two K (splitDoublingNBlock c K K') (tMat c K) rfl hNT

end GlobalTheory.SplitDblGen
end
