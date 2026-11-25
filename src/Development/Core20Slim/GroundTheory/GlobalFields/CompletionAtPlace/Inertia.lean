module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Galois
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Degree
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.Uniqueness
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.IsGaloisGroup.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Separable
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField

open scoped WithZero Pointwise

namespace GroundTheory.Global

section Residue

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem exists_sub_ringOfIntegersToInteger_mem (x : 𝒪[u.adicCompletion F]) :
    ∃ r : 𝓞 F, x - ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] := by
  obtain ⟨r, hr⟩ := toResidueInteger_surjective u (Ideal.Quotient.mk _ x)
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩

theorem ringOfIntegersToInteger_mem_maximalIdeal_iff (r : 𝓞 F) :
    ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] ↔ r ∈ u.asIdeal := by
  rw [← ker_toResidueInteger u, RingHom.mem_ker, toResidueInteger, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem natCard_residueField_integer :
    Nat.card 𝓀[u.adicCompletion F] = Nat.card (𝓞 F ⧸ u.asIdeal) :=
  (Nat.card_congr (residueEquivInteger u).toEquiv).symm

end Residue

section Inertia

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem integerAlgEquiv_ringOfIntegersToInteger (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (r : 𝓞 L) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) (decompositionToLocal v w σ)
        (ringOfIntegersToInteger w r) = ringOfIntegersToInteger w ((σ : Gal(L/K)) • r) := by
  apply Subtype.ext
  rw [coe_integerAlgEquiv_apply, coe_ringOfIntegersToInteger, coe_ringOfIntegersToInteger,
    decompositionToLocal_algebraMap]
  rfl

theorem integerAlgEquiv_mem_maximalIdeal_iff (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (x : 𝒪[w.adicCompletion L]) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) τ x ∈ 𝓂[w.adicCompletion L] ↔
      x ∈ 𝓂[w.adicCompletion L] := by
  simpa using integerAlgEquiv_mem_maximalIdeal_pow_iff τ 1 x

end Inertia

section Frobenius

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

def arithFrobAtDecomposition : MulAction.stabilizer Gal(L/K) w.asIdeal :=
  ⟨arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal, IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) w.asIdeal⟩


omit [NumberField L] [IsGalois K L] [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in
theorem natCard_residueField_eq_under :
    Nat.card 𝓀[v.adicCompletion K] = Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) := by
  rw [natCard_residueField_integer v, ← Ideal.over_def w.asIdeal v.asIdeal]

theorem isArithFrobAt_iff_decompositionToLocal (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal ↔
      ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈
          𝓂[w.adicCompletion L] := by
  rw [natCard_residueField_eq_under v w]
  change (∀ r : 𝓞 L, (σ : Gal(L/K)) • r - r ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈
    w.asIdeal) ↔ _
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := exists_sub_ringOfIntegersToInteger_mem w x
    set q := Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K))
    have h1 := (integerAlgEquiv_mem_maximalIdeal_iff v w (decompositionToLocal v w σ) _).2 hr
    rw [map_sub] at h1
    have h2 : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
          ringOfIntegersToInteger w r ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
        ringOfIntegersToInteger_mem_maximalIdeal_iff]
      exact h r
    have h3 : ringOfIntegersToInteger w r ^ q - x ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [← Ideal.Quotient.eq, map_pow, map_pow, Ideal.Quotient.eq.2 hr]
    have : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ q =
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) x - integerAlgEquiv (v.adicCompletion K)
            (w.adicCompletion L) (decompositionToLocal v w σ) (ringOfIntegersToInteger w r)) +
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
            ringOfIntegersToInteger w r ^ q) + (ringOfIntegersToInteger w r ^ q - x ^ q) := by
      ring
    rw [this]
    exact add_mem (add_mem h1 h2) h3
  · intro h r
    have := h (ringOfIntegersToInteger w r)
    rwa [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
      ringOfIntegersToInteger_mem_maximalIdeal_iff] at this


omit [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in
theorem natCard_inertia :
    Nat.card (w.asIdeal.inertia Gal(L/K)) = w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K)]

theorem eq_decompositionToLocal_arithFrobAt (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (hτ : ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
      τ x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈ 𝓂[w.adicCompletion L]) :
    τ = decompositionToLocal v w (arithFrobAtDecomposition w) := by
  obtain ⟨σ, rfl⟩ := (decompositionToLocal_bijective v w).2 τ
  congr 1
  have hσ : IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal :=
    (isArithFrobAt_iff_decompositionToLocal v w σ).2 hτ
  have hmem := hσ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal)
  have hbot : w.asIdeal.inertia Gal(L/K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ ((natCard_inertia v w).trans he)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact Subtype.ext hmem

end Frobenius

section InertiaGalois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

end InertiaGalois

end GroundTheory.Global
