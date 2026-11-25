module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SatakeDualWeyl.StatementE
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
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
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

namespace GlobalTheory.LocValSplit
open GlobalTheory.LFun (LvTw_eq eulerFac_eq_prod etaU locL etaFam_of_unram eulerFac_singleton mem_aboveF)

theorem LvTw_div_dv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (s : ℂ), IsSplit (E := E) v → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → m w * m w' = 1 → LvTw B m v (s + 1 / 2) / dv E r b v s = eulerFac ((B w).map ((m w)⁻¹ * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
  intro F E _ _ _ _ _ B m v w w' r b s hsplit hunr hne hv hqw hqw' hB' hm1
  classical
  set X : ℂ := GlobalTheory.LFun.npow w (-(s + 1 / 2)) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX' : GlobalTheory.LFun.npow w' (-(s + 1 / 2)) = X := by rw [hXdef, GlobalTheory.LFun.npow, GlobalTheory.LFun.npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have e : Formalism.L2.Host.aboveF (L := E) F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v (s + 1 / 2) = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hr1 : eulerFac ((B w).map ((m w)⁻¹ * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val, hμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv, inv_inv, hμ]
    ring
  have hd : dv E r b v s = (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dv]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : etaU E v = 1 := by unfold etaU; rw [if_pos hsplit]
    rw [locL, etaFam_of_unram hunr, hu, one_pow, eulerFac_singleton, Units.val_one, one_mul, GlobalTheory.LFun.npow, qV, hqw]
  rw [hd, div_inv_eq_mul, hL, hr1, hr2]

end GlobalTheory.LocValSplit
