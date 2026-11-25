module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitive
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_unitary_transitive : ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) → (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) → ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) → ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 → hform τ H y y = 0 → ∑ k, a k * y k = 1 → ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | exact GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive <;> assumption)
