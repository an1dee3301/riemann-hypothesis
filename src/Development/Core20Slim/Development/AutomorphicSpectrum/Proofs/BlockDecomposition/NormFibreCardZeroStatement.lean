module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_fibre_card_zero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | exact GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | (intros; apply GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero <;> assumption)
