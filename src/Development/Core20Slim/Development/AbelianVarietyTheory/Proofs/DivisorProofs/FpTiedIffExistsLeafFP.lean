module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledValuationFormula
public import Formalism.HermitianLattices.StatementLat
public import Formalism.HermitianLattices.StatementMaj
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Prime

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesCompare

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

omit [NumberField K] in
theorem localization_mono' {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    {L L' : Submodule (𝓞 K) W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem primePow_anti (w : HeightOneSpectrum (𝓞 K)) {n n' : ℤ} (h : n' ≤ n) : primePow w n ≤ primePow w n' := by
  have hP : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  obtain ⟨k, rfl⟩ := Int.le.dest h
  have h1 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one
  have h2 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (n' + (k : ℤ)) ≤
      (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' := by
    rw [zpow_add₀ hP, zpow_natCast]
    calc _ ≤ (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' * 1 := by gcongr
      _ = _ := mul_one _
  exact FractionalIdeal.coe_le_coe.mpr h2

theorem scaledAt_anti {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) {n n' : ℤ}
    (h : n' ≤ n) : scaledAt w n B ≤ scaledAt w n' B := by
  refine localization_mono' _ (Submodule.span_mono ?_)
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, primePow_anti w h ha, x, hx, rfl⟩

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

end GlobalTheory.FinitePlacesCompare
