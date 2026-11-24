module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeriesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidueMultisetEqOfShiftedSeriesEqStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfDominantWeightsLowestAlcoveLinkedStatement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem eq_of_hcVal_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  intro p hp k _ _ N ν μ hν hμ hb hval
  have hS : PowerSeries.mk (hcVal k fun i => (μ i : k)) = PowerSeries.mk (hcVal k fun i => (ν i : k)) := by
    ext j
    simp [hval j]
  have gμ := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (μ i : k))
  have gν := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (ν i : k))
  rw [hS] at gμ
  have cast : ∀ (w : Fin N → ℕ) (i : Fin N),
      shift k (fun i => (w i : k)) i = ((w i + (N - 1 - i.val) : ℕ) : k) := by
    intro w i
    simp [shift]
  simp only [cast] at gμ gν
  refine GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked p N hp ν μ hν hμ hb ?_
  refine GlobalTheory.T.residue_multiset_eq_of_shifted_series_eq p hp k N (fun i => ν i + (N - 1 - i.val)) (fun i => μ i + (N - 1 - i.val)) ?_
  rw [← gν, ← gμ]
  ring

end GlobalTheory.Alc
