module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.WithZero
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.Doubling.AbsSplit

theorem norm_eq_zpow {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a : Fv F v} (ha : a ≠ 0) :
    ‖a‖ = (qV F v : ℝ) ^ (-ordL a) := by
  have h0 : Valued.v a ≠ 0 := (map_ne_zero _).2 ha
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0, ordL, dite_eq_right h0, neg_neg]
  simp [qV, WithZero.toAdd_unzero_eq_log h0]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem absEv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV E w : ℝ) ^ (-(ordL (toCompl h x.1) + ordL (toCompl h' x.1))) := by
  intro F E _ _ _ _ _ σ hE v w h w' h' hne x
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq hE hne h h'
  obtain ⟨τ', hτ', -⟩ := existsUnique_splitPrime_eq hE hne.symm h' h
  obtain rfl : τ' = τ.comp σ := (eq_or_eq_comp_conj hE τ τ').resolve_left fun e => hne (hτ.symm.trans (e ▸ hτ'))
  have hN : Algebra.norm (Fv F v) x.1 = splitProj τ x.1 * splitProj (τ.comp σ) x.1 := by
    have := congrArg (splitProj τ) (algebraMap_norm_eq hE x.1)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  have hq : qV E w = qV F v := hτ ▸ GlobalTheory.LFun.SplitTie.qV_splitPrime τ
  have e1 : ordL (toCompl h x.1) = ordL (splitProj τ x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, GlobalTheory.LFun.ConjPlace.valued_complMap hE h hτ])
  have e2 : ordL (toCompl h' x.1) = ordL (splitProj (τ.comp σ) x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', GlobalTheory.LFun.ConjPlace.valued_complMap hE h' hτ'])
  have hq0 : (qV F v : ℝ) ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    unfold qV
    exact_mod_cast (by omega)
  rw [absEv_apply, coe_nnnorm, hN, norm_mul, hq, e1, e2, neg_add, zpow_add₀ hq0,
    norm_eq_zpow v (x.isUnit.map (splitProj τ)).ne_zero, norm_eq_zpow v (x.isUnit.map (splitProj (τ.comp σ))).ne_zero]

end GlobalTheory.Doubling.AbsSplit
