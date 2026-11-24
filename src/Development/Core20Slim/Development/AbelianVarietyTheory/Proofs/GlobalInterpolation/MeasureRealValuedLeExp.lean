module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsResidueEqZeroIff
public import Batteries.Logic
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Ext
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
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
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Init
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.HaarLatticeScale

theorem exists_valued_eq_exp (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (n : ℤ) : ∃ a : Fv F v, Valued.v a = WithZero.exp n := by
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp n)
  exact ⟨a, ha⟩

theorem lt_one_iff_le_exp (t : WithZero (Multiplicative ℤ)) :
    t < 1 ↔ t ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne t 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem step (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type)
    [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι]
    (e : V ≃L[Fv F v] (ι → Fv F v)) (n : ℤ) :
    μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp (n - 1)} *
      (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ Fintype.card ι =
    μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp F v (-n)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  let e' : V ≃L[Fv F v] (ι → Fv F v) := e.trans
    (ContinuousLinearEquiv.piCongrRight fun _ : ι =>
      ContinuousLinearEquiv.unitsEquivAut (Fv F v) (Units.mk0 a ha0))
  have he' : ∀ x i, e' x i = e x i * a := fun x i => by
    simp [e']
  have hv : ∀ (y : Fv F v) (m : ℤ),
      Valued.v (y * a) ≤ WithZero.exp m ↔ Valued.v y ≤ WithZero.exp (n + m) := by
    intro y m
    rw [map_mul, ha, WithZero.exp_neg, mul_inv_le_iff₀ WithZero.exp_pos, ← WithZero.exp_add,
      add_comm]
  have h := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v V μ ι e' {0}
  have h1 : {x | ∀ i, e' x i ∈ v.adicCompletionIntegers F} =
      {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} := by
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, he', ← WithZero.exp_zero, hv, add_zero]
  have hres : ∀ y : v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 ↔
        Valued.v (y : Fv F v) ≤ WithZero.exp (-1 : ℤ) := by
    intro y
    rw [IsLocalRing.residue_eq_zero_iff, ← lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  have h2 : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e' x i = (y i : Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈
        ({0} : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} =
      {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp (n - 1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, funext_iff, Pi.zero_apply, hres]
    constructor
    · rintro ⟨y, hy, hy'⟩ i
      rw [sub_eq_add_neg, ← hv, ← he', hy]
      exact hy' i
    · intro hx
      have hx' : ∀ i, Valued.v (e' x i) ≤ WithZero.exp (-1 : ℤ) := fun i => by
        rw [he', hv, ← sub_eq_add_neg]
        exact hx i
      refine ⟨fun i => ⟨e' x i, ?_⟩, fun i => rfl, hx'⟩
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact ((lt_one_iff_le_exp _).2 (hx' i)).le
  rw [h1, h2] at h
  simpa using h

theorem measureReal_valued_le_exp : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (e : V ≃L[Fv F v] (ι → Fv F v)) (n : ℤ), μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} = ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ n) ^ Fintype.card ι * μ.real {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} := by
  intro F _ _ v V _ _ _ _ _ _ μ _ ι _ e n
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hq : (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hs := step F v V μ ι e
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ)
  induction n using Int.induction_on with
  | zero =>
    simp only [zpow_zero, one_pow, one_mul, WithZero.exp_zero]
    rfl
  | succ k ih =>
    rw [← hs, add_sub_cancel_right, ih, zpow_add_one₀ hq, mul_pow]
    ring
  | pred k ih =>
    apply mul_right_cancel₀ (pow_ne_zero (Fintype.card ι) hq)
    rw [hs, ih, zpow_sub_one₀ hq, mul_pow, inv_pow]
    field_simp

end GlobalTheory.HaarLatticeScale
