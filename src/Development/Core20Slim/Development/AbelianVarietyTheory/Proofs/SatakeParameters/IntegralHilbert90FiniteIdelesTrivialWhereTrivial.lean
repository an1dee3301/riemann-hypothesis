module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
public import Formalism.LocalToGlobal.Divisibility.TuplesLemmas
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwU.IntegralHilbert90Unramified
open GlobalTheory.AdeleBaseChange 


theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem locMap_val_eq_one_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F) :
    Valued.v (locMap F P a) = 1 ↔ Valued.v a = 1 := by
  have hle : ∀ b : (P.under (𝓞 F)).adicCompletion F, Valued.v b ≤ 1 → Valued.v (locMap F P b) ≤ 1 := fun b hb => by
    simpa using locMap_valued P 0 b (by simpa using hb)
  have hlt : ∀ b : (P.under (𝓞 F)).adicCompletion F, Valued.v b < 1 → Valued.v (locMap F P b) < 1 := fun b hb => by
    have := locMap_valued P 1 b (by simpa using le_exp_neg_one_of_lt_one hb)
    refine lt_of_le_of_lt this ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hg
    · exact absurd h (ne_of_lt (hlt a hl))
    · have ha0 : a ≠ 0 := fun e => by rw [e, map_zero] at hg; exact not_lt_of_ge zero_le' hg
      have hinv : Valued.v a⁻¹ < 1 := by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ hg
      have h2 := hlt _ hinv
      rw [map_inv₀, map_inv₀, h, inv_one] at h2
      exact lt_irrefl _ h2
  · intro h
    have ha0 : a ≠ 0 := fun e => by rw [e, map_zero] at h; exact zero_ne_one h
    refine le_antisymm (hle a h.le) ?_
    have h2 := hle a⁻¹ (by rw [map_inv₀, h, inv_one])
    have h3 : Valued.v (locMap F P a) * Valued.v (locMap F P a⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (locMap F P a) * Valued.v (locMap F P a⁻¹) := h3.symm
      _ ≤ Valued.v (locMap F P a) := mul_le_of_le_one_right' h2



variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_sig_notMem (σ : E →ₐ[F] E) (hσ : IsConjOf σ) [Algebra.Unramified (𝓞 F) (𝓞 E)]
    (P : HeightOneSpectrum (𝓞 E)) : ∃ b : 𝓞 E, b - RingOfIntegers.mapAlgHom σ b ∉ P.asIdeal := by
  by_contra hn
  push_neg at hn
  have h := Algebra.FormallyUnramified.ext_of_iInf (R := 𝓞 F) P.asIdeal
    (Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top) (g₁ := AlgHom.id _ (𝓞 E))
    (g₂ := RingOfIntegers.mapAlgHom σ) (fun x => Ideal.Quotient.eq.2 (hn x))
  apply hσ.1
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have h1 : ∀ a : 𝓞 E, σ (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a := fun a => by
    have := DFunLike.congr_fun h a
    exact congrArg (algebraMap (𝓞 E) E) this.symm
  rw [map_div₀, h1, h1]
  rfl



end GlobalTheory.TwU.IntegralHilbert90Unramified

