module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeterminantIdealHermitianLatticeBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_determinantIdeal_hermitianLattice_basis : ∀ (D : D7) (N N' r : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ x ∈ Y, ∀ y ∈ Y, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → (∀ i, ∃ s : ℕ, 0 < s ∧ (s : D.host.E) • b₀ i ∈ Y) → ∃ I : Submodule (𝓞 D.host.K) D.host.K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : D.host.K) * x ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧ ∀ (p : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p Y b → (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det ∈ I) ∧ ∀ x ∈ I, ∃ (s : ℕ) (c : 𝓞 D.host.K), Nat.Coprime s p ∧ (s : D.host.K) * x = (c : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det := by
  first | exact @GlobalTheory.NormSum.exists_detIdeal | exact GlobalTheory.NormSum.exists_detIdeal | (intros; apply GlobalTheory.NormSum.exists_detIdeal <;> assumption)
