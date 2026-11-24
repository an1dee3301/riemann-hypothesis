module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchy
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.UniformSpace.Cauchy

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ a : ℕ → L, (∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (a (k + 1) - a k)) →
    ∃ b : L, ∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (b - a k) := by
  first | exact @GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | exact GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | (intros; apply GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow <;> assumption)
