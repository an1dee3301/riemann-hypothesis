module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.WithZero
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.AbsInert

theorem ordL_eq_neg_log {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {y : L}
    (hy : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ))) : ordL y = -WithZero.log (Valued.v y) := by
  unfold ordL
  rw [dite_eq_right hy, WithZero.toAdd_unzero_eq_log]

theorem absEv_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV F v : ℝ) ^ (-(2 * ordL (toCompl h x.1))) := by
  intro F E _ _ _ _ _ σ hσ v w h hw x

  set N : Fv F v := Algebra.norm (Fv F v) x.1 with hNdef
  set z : w.adicCompletion E := toCompl h x.1 with hzdef
  have hN0 : N ≠ 0 := ((x.isUnit.map (Algebra.norm (Fv F v))).ne_zero)
  have hz0 : z ≠ 0 := (x.isUnit.map (toCompl h)).ne_zero

  have key := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x.1
  have key' := congrArg (toCompl h) key
  rw [map_mul] at key'
  have hl : toCompl h (algebraMap (Fv F v) (Fv F v ⊗[F] E) N) = GlobalTheory.LFun.complMap h N := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [hl] at key'

  let c : w.adicCompletion E →+* w.adicCompletion E :=
    (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp
      (((sigR (Fv F v) σ : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E)).comp (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom)
  have he : ∀ t, GlobalTheory.LFun.InertChart.complEquiv hw h t = toCompl h t := fun _ => rfl
  have hs : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm z = x.1 := by
    rw [RingEquiv.symm_apply_eq, he]
  have hcz : c z = toCompl h (sigR (Fv F v) σ x.1) := by
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) = _
    rw [hs, he]
  have hc : GlobalTheory.LFun.IsConjAt σ h c := by
    unfold GlobalTheory.LFun.IsConjAt
    intro t
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (toCompl h t))) = _
    rw [← he t, RingEquiv.symm_apply_apply, he]

  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hσ hw hc
  have hvc : Valued.v (toCompl h (sigR (Fv F v) σ x.1)) = Valued.v z := by
    rw [← hcz]
    exact hU.2.1 z

  have he1 : w.asIdeal.ramificationIdx (𝓞 F) = 1 :=
    GlobalTheory.LFun.isUnram_iff.mp (GlobalTheory.LFun.isUnram_of_isInertAt hw) w h
  have hvN : Valued.v N = Valued.v z ^ 2 := by
    have hv := GlobalTheory.LFun.valued_complMap h hN0
    rw [he1, pow_one, key', map_mul, hvc] at hv
    rw [sq]
    exact hv.symm
  have hz' : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  have hN' : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).mpr hN0

  rw [GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
  show ‖N‖ = _
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hN',
    hvN, WithZero.log_pow, ordL_eq_neg_log (y := toCompl h x.1) hz']
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) = (qV F v : ℝ) := by simp [qV]
  rw [NNReal.coe_zpow, hq]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.AbsInert

end
