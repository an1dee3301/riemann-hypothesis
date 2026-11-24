module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraLast
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
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
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkewScale

variable {E : Type} [Field E] [NumberField E]

theorem exists_intValuation_eq {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 E))
    (hw : Function.Injective w) (k : ι → ℕ) :
    ∃ a : 𝓞 E, ∀ i, (w i).intValuation a = WithZero.exp (-(k i : ℤ)) := by
  classical
  choose π hπ using fun i => (w i).intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := (Finset.univ : Finset ι))
    (fun i => (w i).asIdeal) (fun i => k i + 1) (fun i _ => (w i).prime)
    (fun i _ j _ hij e => hij (hw (HeightOneSpectrum.ext e))) (fun i => π i.1 ^ k i.1)
  refine ⟨a, fun i => ?_⟩
  have h1 : (w i).intValuation (π i ^ k i) = WithZero.exp (-(k i : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have h2 := ((w i).intValuation_le_pow_iff_mem _ _).2 (ha i (Finset.mem_univ i))
  rw [← h1]
  apply Valuation.map_eq_of_sub_lt
  rw [h1]
  refine lt_of_le_of_lt h2 ?_
  rw [WithZero.exp_lt_exp]
  push_cast
  omega

theorem exists_valuation_eq {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 E))
    (hw : Function.Injective w) (t : ι → WithZero (Multiplicative ℤ)) (ht : ∀ i, t i ≠ 0) :
    ∃ c : E, c ≠ 0 ∧ ∀ i, (w i).valuation E c = t i := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_ne_zero, fun i => isEmptyElim i⟩
  obtain ⟨a, ha⟩ := exists_intValuation_eq w hw (fun i => (-(t i).log).toNat)
  obtain ⟨b, hb⟩ := exists_intValuation_eq w hw (fun i => ((t i).log).toNat)
  have hne : ∀ r : 𝓞 E, (w i₀).intValuation r ≠ 0 → algebraMap (𝓞 E) E r ≠ 0 := fun r hr e => by
    apply hr
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 e, map_zero]
  have ha0 := hne a (by rw [ha]; exact WithZero.exp_ne_zero)
  have hb0 := hne b (by rw [hb]; exact WithZero.exp_ne_zero)
  refine ⟨algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b, div_ne_zero ha0 hb0, fun i => ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, ha, hb,
    ← WithZero.exp_sub]
  conv_rhs => rw [← WithZero.exp_log (ht i)]
  congr 1
  omega

end GlobalTheory.PlaneSkewScale

namespace GlobalTheory.PlaneSkewScale

variable {E : Type} [Field E] [NumberField E]

theorem exists_smul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (x : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  exact GlobalTheory.NonzeroSmulMembership.exists_ne_zero_smul_mem L hL x

theorem exists_max {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) {x : Fin n → E} (hx : x ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ s₀ : E, s₀ ≠ 0 ∧ s₀ • x ∈ L ∧ ∀ s : E, s • x ∈ L → w.valuation E s ≤ w.valuation E s₀ := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  obtain ⟨G, hG⟩ := hL.fg
  set B := G.sup fun g => w.valuation E (g j)
  have hB : ∀ z ∈ L, w.valuation E (z j) ≤ B := by
    intro z hz
    rw [← hG] at hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact Finset.le_sup (f := fun g => w.valuation E (g j)) hz
    | zero => simp
    | add z₁ z₂ _ _ h₁ h₂ => rw [Pi.add_apply]; exact Valuation.map_add_le _ h₁ h₂
    | smul a z _ h =>
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      exact mul_le_of_le_one_left' (w.valuation_le_one a) |>.trans h
  have hxj : w.valuation E (x j) ≠ 0 := (map_ne_zero _).2 (by simpa using hj)
  have hbound : ∀ s : E, s • x ∈ L → w.valuation E s ≤ B * (w.valuation E (x j))⁻¹ := fun s hs => by
    have := hB _ hs
    rw [Pi.smul_apply, smul_eq_mul, map_mul] at this
    exact (le_mul_inv_iff₀ (zero_lt_iff.2 hxj)).2 this
  obtain ⟨K, hK⟩ : ∃ K : ℤ, B * (w.valuation E (x j))⁻¹ ≤ WithZero.exp K := by
    by_cases h0 : B * (w.valuation E (x j))⁻¹ = 0
    · exact ⟨0, by rw [h0]; exact zero_le'⟩
    · exact ⟨_, (WithZero.exp_log h0).ge⟩
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem L hL x
  have hd' : algebraMap (𝓞 E) E d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hd
  let S : ℤ → Prop := fun k => ∃ s : E, s ≠ 0 ∧ s • x ∈ L ∧ w.valuation E s = WithZero.exp k
  obtain ⟨k₀, ⟨s₀, hs₀, hs₀L, hs₀v⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := S)
    ⟨K, fun k ⟨s, _, hs, hv⟩ => by
      have := (hbound s hs).trans hK
      rwa [hv, WithZero.exp_le_exp] at this⟩
    ⟨_, algebraMap (𝓞 E) E d, hd', by rwa [algebraMap_smul],
      (WithZero.exp_log ((map_ne_zero _).2 hd')).symm⟩
  refine ⟨s₀, hs₀, hs₀L, fun s hs => ?_⟩
  by_cases h0 : s = 0
  · rw [h0, map_zero]; exact zero_le'
  · have hv := (WithZero.exp_log ((map_ne_zero (w.valuation E)).2 h0)).symm
    rw [hv, hs₀v, WithZero.exp_le_exp]
    exact hmax _ ⟨s, h0, hs, hv⟩

theorem primAt_smul {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    {c s₀ : E} (hc : c ≠ 0) (hs₀ : s₀ • x ∈ L) (hmax : ∀ s : E, s • x ∈ L → w.valuation E s ≤ w.valuation E s₀)
    (he : w.valuation E c = w.valuation E s₀) : PrimAt w L (c • x) := by
  have hc' : w.valuation E c ≠ 0 := (map_ne_zero _).2 hc
  refine ⟨fun s hs => ?_, s₀ * c⁻¹, ?_, ?_⟩
  · rw [smul_smul] at hs
    have h1 := hmax _ hs
    rw [map_mul, ← he] at h1
    have h2 : w.valuation E s * w.valuation E c ≤ 1 * w.valuation E c := by rwa [one_mul]
    have h3 : w.valuation E s ≤ 1 * w.valuation E c * (w.valuation E c)⁻¹ := (le_mul_inv_iff₀ (zero_lt_iff.2 hc')).2 h2
    rwa [one_mul, mul_inv_cancel₀ hc'] at h3
  · rwa [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · rw [map_mul, map_inv₀, ← he, mul_inv_cancel₀ hc']

end GlobalTheory.PlaneSkewScale

namespace GlobalTheory.PlaneSkewScale

theorem exists_rescale_primAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 →
    ∀ (P : Finset (HeightOneSpectrum (𝓞 F))) (τ : ∀ v : P, E →ₐ[F] Fv F v.1), ∃ c : E, c ≠ 0 ∧
      ∀ v : P, PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L (c • x) ∧ PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L ((σ c)⁻¹ • y) := by
  intro F E _ _ _ _ _ σ hσ n L hL x y hx hy P τ
  classical
  choose sx hsx0 hsxL hsxmax using fun v : P => exists_max L hL hx (GlobalTheory.AdelicU.splitPrime (τ v))
  choose sy hsy0 hsyL hsymax using fun v : P => exists_max L hL hy (GlobalTheory.AdelicU.splitPrime (τ v))
  let w : P ⊕ P → HeightOneSpectrum (𝓞 E) :=
    Sum.elim (fun v => GlobalTheory.AdelicU.splitPrime (τ v)) (fun v => GlobalTheory.AdelicU.splitPrime ((τ v).comp σ))
  have hunder : ∀ i, (w i).under (𝓞 F) = (Sum.elim (fun v : P => v.1) (fun v : P => v.1) i) := by
    rintro (v | v) <;> exact GlobalTheory.AdelicU.splitPrime_under _
  have hw : Function.Injective w := by
    intro i j e
    have hv := (hunder i).symm.trans ((congrArg (fun u => u.under (𝓞 F)) e).trans (hunder j))
    rcases i with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases j with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hv <;> subst hv
    · rfl
    · exact absurd e.symm (GlobalTheory.AdelicU.splitPrime_comp_ne hσ _)
    · exact absurd e (GlobalTheory.AdelicU.splitPrime_comp_ne hσ _)
    · rfl
  let t : P ⊕ P → WithZero (Multiplicative ℤ) :=
    Sum.elim (fun v => (GlobalTheory.AdelicU.splitPrime (τ v)).valuation E (sx v))
      (fun v => ((GlobalTheory.AdelicU.splitPrime (τ v)).valuation E (sy v))⁻¹)
  obtain ⟨c, hc0, hc⟩ := exists_valuation_eq w hw t (by
    rintro (v | v)
    · exact (map_ne_zero _).2 (hsx0 v)
    · exact inv_ne_zero ((map_ne_zero _).2 (hsy0 v)))
  refine ⟨c, hc0, fun v => ⟨primAt_smul hc0 (hsxL v) (hsxmax v) (hc (Sum.inl v)),
    primAt_smul (inv_ne_zero ((map_ne_zero σ).2 hc0)) (hsyL v) (hsymax v) ?_⟩⟩
  have h1 := hc (Sum.inr v)
  simp only [w, t, Sum.elim_inr] at h1
  rw [← GlobalTheory.AdelicU.valued_apply_eq_valuation, AlgHom.comp_apply, GlobalTheory.AdelicU.valued_apply_eq_valuation] at h1
  rw [map_inv₀, h1, inv_inv]

end GlobalTheory.PlaneSkewScale
