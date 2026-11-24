module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SatakeDualWeyl.StatementG
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace GlobalTheory.InertConjVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phiO (φ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (φ : E →+* E)

theorem coe_phiO (φ : E →ₐ[F] E) (y : 𝓞 E) : ((phiO φ y : 𝓞 E) : E) = φ (y : E) := rfl

theorem phiO_comp (φ : E →ₐ[F] E) :
    (phiO φ).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := by
  refine RingHom.ext fun f => RingOfIntegers.ext ?_
  rw [RingHom.comp_apply, coe_phiO]
  have h : ((algebraMap (𝓞 F) (𝓞 E) f : 𝓞 E) : E) = algebraMap F E (f : F) := rfl
  rw [h]
  exact φ.commutes _

theorem map_phiO_pow (φ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    Ideal.map (phiO φ) (w.asIdeal ^ n) = w.asIdeal ^ n := by
  unfold Formalism.UG.IsInertAt at hin
  rw [← hin, ← Ideal.map_pow, Ideal.map_map, phiO_comp]

theorem intVal_phi_le (φ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (y : 𝓞 E) :
    w.intValuation (phiO φ y) ≤ w.intValuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [map_zero]
  have h0 : w.intValuation y ≠ 0 := w.intValuation_ne_zero y hy
  have h1 : w.intValuation y ≤ 1 := w.intValuation_le_one y
  set k := WithZero.log (w.intValuation y) with hk
  have hek : w.intValuation y = WithZero.exp k := (WithZero.exp_log h0).symm
  have hk0 : k ≤ 0 := by
    rw [hek, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  have hn : w.intValuation y = WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) := by
    rw [hek, Int.toNat_of_nonneg (by omega), neg_neg]
  have hm : y ∈ w.asIdeal ^ (-k).toNat := (w.intValuation_le_pow_iff_mem y _).1 hn.le
  rw [hn]
  refine (w.intValuation_le_pow_iff_mem _ _).2 ?_
  rw [← map_phiO_pow φ v w hin]
  exact Ideal.mem_map_of_mem _ hm

theorem bij (σ : E →ₐ[F] E) : Function.Bijective σ := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact σ.bijective

theorem intVal_phi (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (y : 𝓞 E) :
    w.intValuation (phiO σ y) = w.intValuation y := by
  refine le_antisymm (intVal_phi_le σ v w hin y) ?_
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (bij σ)
  have h := intVal_phi_le (τ.symm : E →ₐ[F] E) v w hin (phiO σ y)
  have e : phiO (τ.symm : E →ₐ[F] E) (phiO σ y) = y := by
    apply RingOfIntegers.ext
    rw [coe_phiO, coe_phiO]
    show τ.symm (τ (y : E)) = (y : E)
    exact τ.symm_apply_apply _
  rwa [e] at h

theorem val_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : E, w.valuation E (σ x) = w.valuation E x := by
  intro F E _ _ _ _ _ σ v w hin x
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, map_div₀, map_div₀]
  have e : ∀ y : 𝓞 E, σ (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E (phiO σ y) := fun y => rfl
  rw [e, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intVal_phi σ v w hin, intVal_phi σ v w hin]

end GlobalTheory.InertConjVal
