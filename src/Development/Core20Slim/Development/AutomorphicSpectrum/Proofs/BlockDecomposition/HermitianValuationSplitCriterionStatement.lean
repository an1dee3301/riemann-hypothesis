module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianValuationSplitCriterion
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_valuation_split_criterion : ∀ {k R V : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0), (∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) → (∀ a, c (c a) = a) → (∀ a, c a = a → ∃ x : k, algebraMap k R x = a) → (∀ x : k, c (algebraMap k R x) = algebraMap k R x) → (∀ a, a ∈ 𝔬 ↔ W a ≤ 1) → (∀ a, W (c a) = W a) → (∀ a, W a = 0 → a = 0) → (∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) → ∀ h : V → V → R, IsHerm c h → (∀ z, h z z = 0 → z = 0) → ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even | exact GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even | (intros; apply GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even <;> assumption)
