module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpace
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_orthonormal_frames_hermitian_space : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | exact GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples <;> assumption)
