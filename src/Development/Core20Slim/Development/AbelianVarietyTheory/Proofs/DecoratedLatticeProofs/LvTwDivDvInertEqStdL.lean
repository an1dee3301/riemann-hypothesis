module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Nat
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem LvTw_div_dv_inert_eq_stdL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (α : Fin (r / 2) → ℂˣ) (s : ℂ), Module.finrank F E = 2 → IsInertAt F E v w → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → B w = bcParam r α → LvTw B m v (s + 1 / 2) / dv E r b v s = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (qV F v) r α (((m w)⁻¹ : ℂˣ) : ℂ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (qV F v) r b s := by
  intro F E _ _ _ _ _ B m v w r b α s h2 hw hU hB
  have hv := InertChart.under_eq_iff hw
  have hq := InertChart.absNorm_eq h2 hw
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (one_lt_absNorm v).ne_bot
  have hns := not_isSplit_of_isInertAt hw
  rw [LvTw_inert B m hv hq, hB]
  congr 1
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL, Units.val_inv_eq_inv_val]
    congr 2
    rw [npow, show qV F v = Ideal.absNorm v.asIdeal from rfl, pow_two,
      show -(2 * (s + 1 / 2)) = -(s + 1 / 2) + -(s + 1 / 2) by ring, Complex.cpow_add _ _ hq0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  · rw [dv, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [locL, etaFam_of_unram hU, eulerFac_singleton, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.etaL, Units.val_pow_eq_pow_val, npow,
      show qV F v = Ideal.absNorm v.asIdeal from rfl]
    have he : ((etaU E v : ℂˣ) : ℂ) = -1 := by simp [etaU, hns]
    rw [he]

end GlobalTheory.LFun
