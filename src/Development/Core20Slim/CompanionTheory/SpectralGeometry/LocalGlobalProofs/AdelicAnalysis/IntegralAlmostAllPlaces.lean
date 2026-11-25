module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
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
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodInt

theorem valued_algebraMap {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem eventually_le_one {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun v hv => ?_
  exact not_le.mp hv

theorem eventually_eq_one {F : Type} [Field F] [NumberField F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 := by
  filter_upwards [eventually_le_one x, eventually_le_one x⁻¹] with v h1 h2
  refine le_antisymm h1 ?_
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  exact (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2

theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem rational_integral_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  intro F E _ _ _ _ _ σ _ d b
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have h : ∀ k : Fin d, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        v.valuation F (b.repr x k) ≤ 1 := fun k => eventually_le_one _
    filter_upwards [Filter.eventually_all.mpr h] with v hv k
    rw [repr_inclR, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    exact hv k
  · filter_upwards [eventually_eq_one x hx] with v hv
    rw [valued_algebraMap, hv]

end GlobalTheory.CompanionTheory.SW.GoodInt
