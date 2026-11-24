module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacterStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix

namespace GlobalTheory.PairingTraceExpansion

variable {K : Type} [Field K] {n d : ℕ}

theorem pair_eq_trace (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = trace (Xᵀ * Y) := by
  simp only [GlobalTheory.FlipMatch.pairM, trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem pair_expand (P M : Matrix (Fin n) (Fin d) K) :
    trace (Pᵀ * M) = ∑ i : Fin n, ∑ j : Fin d, P i j * M i j := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem main (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
      (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  have hb : (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (↑b : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have ht : ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * (↑c⁻¹ : Matrix (Fin d) (Fin d) K)ᵀ)ᵀ *
      -((↑b : Matrix (Fin n) (Fin n) K)ᵀ * A * Q * Bᵀ * (↑c : Matrix (Fin d) (Fin d) K)) =
      -((↑c⁻¹ : Matrix (Fin d) (Fin d) K) * (Pᵀ * (A * Q * Bᵀ)) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, neg_inj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ, hb, Matrix.one_mul]
  rw [pair_eq_trace, ht, trace_neg, trace_mul_comm, ← Matrix.mul_assoc, hc, Matrix.one_mul, pair_expand]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

end GlobalTheory.PairingTraceExpansion
