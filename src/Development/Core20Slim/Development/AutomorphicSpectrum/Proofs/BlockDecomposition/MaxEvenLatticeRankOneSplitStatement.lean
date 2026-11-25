module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeRankOneSplit
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Init.Core
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.max_even_lattice_rank_one_split : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (O : ValuationSubring k) (φ : R ≃+* k × k) (c : R →+* R) (𝔬 : Subring R), (∀ r, φ (c r) = (φ r).swap) → (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ h : V → V → R, IsHerm c h → ∀ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) → IsUnit (h w₀ w₀) → ∀ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → ∀ α β : k, (∀ r : R, r • w₀ ∈ L ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y)) → α ≠ 0 ∧ β ≠ 0 ∧ ∃ u : k, u ∈ O ∧ u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u := by
  first | exact @GlobalTheory.CompanionTheory.KFin.RankOne.unimodular_coords | exact GlobalTheory.CompanionTheory.KFin.RankOne.unimodular_coords | (intros; apply GlobalTheory.CompanionTheory.KFin.RankOne.unimodular_coords <;> assumption)
