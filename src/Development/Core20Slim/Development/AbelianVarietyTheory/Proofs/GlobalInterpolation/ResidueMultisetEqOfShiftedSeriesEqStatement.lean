module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidueMultisetEqOfShiftedSeriesEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_multiset_eq_of_shifted_series_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (l l' : Fin N → ℕ), (∏ i, (1 - PowerSeries.C ((l i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l' i : k) * PowerSeries.X) = (∏ i, (1 - PowerSeries.C ((l' i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l i : k) * PowerSeries.X) → ∀ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = (Finset.univ.filter fun i => (l' i : ZMod p) = x).card := by
  first | exact @GlobalTheory.Alc.multiset_eq_of_series_eq | exact GlobalTheory.Alc.multiset_eq_of_series_eq | (intros; apply GlobalTheory.Alc.multiset_eq_of_series_eq <;> assumption)
