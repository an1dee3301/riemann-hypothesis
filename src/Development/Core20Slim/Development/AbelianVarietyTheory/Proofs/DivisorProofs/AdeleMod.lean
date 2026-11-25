module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.AdeleTensorModule

theorem adele_mod (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 1 ≤ N)
    (y : FiniteAdeleRing (𝓞 F) F) (hy : y ∈ Formalism.UG.intAd F) :
    ∃ a : 𝓞 F, ∃ w ∈ Formalism.UG.intAd F,
      y = algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) + (N : FiniteAdeleRing (𝓞 F) F) * w := by
  have hN0 : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨a, ha⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (R := 𝓞 F) (K := F) y hy (N : 𝓞 F) hN0
  refine ⟨a, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹) *
    (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)), fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) ((N : F)⁻¹) *
      (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀]
    have hv : Valued.v (algebraMap F (v.adicCompletion F) (N : F)) = v.intValuation (N : 𝓞 F) := by
      have := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R (K := F) v (N : 𝓞 F)
      rwa [map_natCast (algebraMap (𝓞 F) F)] at this
    have h0 : v.intValuation (N : 𝓞 F) ≠ 0 := v.intValuation_ne_zero _ hN0
    rw [hv]
    calc (v.intValuation (N : 𝓞 F))⁻¹ * Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
        ≤ (v.intValuation (N : 𝓞 F))⁻¹ * v.intValuation (N : 𝓞 F) := by
          gcongr
          exact ha v
      _ = 1 := inv_mul_cancel₀ h0
  · rw [← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hNF, map_one, one_mul]
    ring

theorem tens_mod (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (hN : 1 ≤ N) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hx : x ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) :
    ∃ a ∈ Formalism.UG.intOE E,
      ∃ z ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F),
        x = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a +
          (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z := by
  set S := Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) with hS
  set ι := Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι
  have hl : ∀ a ∈ Formalism.UG.intOE E, ι a ∈ S := fun a ha =>
    Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)
  have hr : ∀ w ∈ Formalism.UG.intAd F, (1 : E) ⊗ₜ[F] w ∈ S := fun w hw =>
    Subring.subset_closure (Or.inr ⟨⟨w, hw⟩, rfl⟩)
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨a, a.2, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩
    · obtain ⟨a, w, hw, e⟩ := adele_mod F N hN y y.2
      refine ⟨algebraMap F E (a : F), ⟨algebraMap (𝓞 F) (𝓞 E) a, rfl⟩, (1 : E) ⊗ₜ[F] w, hr w hw, ?_⟩
      have e2 := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := E)
        (B := FiniteAdeleRing (𝓞 F) F)) e
      rw [map_add (f := _), map_mul, map_natCast, AlgHom.commutes] at e2
      exact e2
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by rw [map_zero, mul_zero, add_zero]⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, by rw [map_one, mul_zero, add_zero]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    obtain ⟨b, hb, w, hw, rfl⟩ := ihy
    exact ⟨a + b, add_mem ha hb, z + w, add_mem hz hw, by rw [map_add (f := _)]; ring⟩
  | neg x _ ihx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    exact ⟨-a, neg_mem ha, -z, neg_mem hz, by rw [map_neg]; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    obtain ⟨b, hb, w, hw, rfl⟩ := ihy
    refine ⟨a * b, mul_mem ha hb, ι a * w + z * ι b + (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * (z * w),
      add_mem (add_mem (mul_mem (hl a ha) hw) (mul_mem hz (hl b hb)))
        (mul_mem (natCast_mem S N) (mul_mem hz hw)), ?_⟩
    rw [map_mul]; ring

theorem main : ∀ {D : Formalism.BasicNotions.D7} (N : ℕ), (1 : ℕ) ≤ N → ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    ∃ a ∈ Formalism.UG.intOE ((Formalism.BasicNotions.D7.host D).E), ∃ z ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
      x = (Formalism.MainNotions.StandardLatticesGL3.inc D : (Formalism.BasicNotions.D7.host D).E → Formalism.MainNotions.StandardLatticesGL3.AE D) a +
        (↑N : Formalism.MainNotions.StandardLatticesGL3.AE D) * z :=
  fun {D} N hN x hx => tens_mod ℚ D.host.E N hN x hx

end GlobalTheory.AdeleTensorModule

end
