module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_integralPoints_membership : ∀ (D : D7) (N : ℕ), (∀ g : GA D N, g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ k : GA D N, k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D))) ∧ (∀ γ : Matrix (Fin N) (Fin N) D.host.E, γ * (γ.map D.host.conj).transpose = 1 → ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ (g : GA D N) γ, IsRat D (g : GL (Fin N) (AE D)) γ → γ * (γ.map D.host.conj).transpose = 1) ∧ Function.Injective (inc D) := by
  first | exact @GlobalTheory.NormSum.mem_ratG_intG | exact GlobalTheory.NormSum.mem_ratG_intG | (intros; apply GlobalTheory.NormSum.mem_ratG_intG <;> assumption)
