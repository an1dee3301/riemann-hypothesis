module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix nonZeroDivisors

namespace GlobalTheory.CompanionTheory.SW.SelfDual

theorem differentExp_finite (F : Type) [Field F] [NumberField F] :
    {v : HeightOneSpectrum (𝓞 F) | GroundTheory.Global.differentExp v ≠ 0}.Finite := by
  unfold GroundTheory.Global.differentExp
  exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)

private theorem differentIdeal_int_ne_zero (F : Type) [Field F] [NumberField F] :
    differentIdeal ℤ (𝓞 F) ≠ 0 := by
  intro h
  have h1 := absNorm_differentIdeal F (𝓞 F)
  rw [h, map_zero] at h1
  exact discr_ne_zero F (Int.natAbs_eq_zero.1 h1.symm)

private theorem differentExp_eq_count_differentIdeal (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    GroundTheory.Global.differentExp v =
      ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors : ℤ) := by
  unfold GroundTheory.Global.differentExp
  exact FractionalIdeal.count_coe F v (differentIdeal_int_ne_zero F)

private theorem prod_absNorm_pow_count_differentIdeal_eq_natAbs_discr (F : Type) [Field F] [NumberField F] :
    ∏ v ∈ (differentExp_finite F).toFinset, Ideal.absNorm v.asIdeal ^
      ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors) =
      (discr F).natAbs := by
  have hprod := Ideal.finprod_heightOneSpectrum_factorization (differentIdeal_int_ne_zero F)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := (differentExp_finite F).toFinset) ?_] at hprod
  · have hN := congrArg Ideal.absNorm hprod
    rw [map_prod, absNorm_differentIdeal F (𝓞 F)] at hN
    rw [← hN]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [HeightOneSpectrum.maxPowDividing, map_pow]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, differentExp_eq_count_differentIdeal]
    intro h0
    apply hv
    have h0' : (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors = 0 := by
      exact_mod_cast h0
    rw [HeightOneSpectrum.maxPowDividing, h0', pow_zero]

theorem sqrt_discr_mul_finprod_different (F : Type) [Field F] [NumberField F] :
    (∀ᶠ v in Filter.cofinite, (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1) ∧ Real.toNNReal (Real.sqrt |(discr F : ℝ)|) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [FractionalIdeal.finite_factors (K := F)
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)] with v hv
    have hv' : GroundTheory.Global.differentExp v = 0 := hv
    rw [hv']
    simp
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := (differentExp_finite F).toFinset) ?_]
    · have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
          (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) =
            ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
              ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors)) ^
                (-(1 / 2 : ℝ)) := by
        intro v
        rw [differentExp_eq_count_differentIdeal, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
        congr 1
        push_cast
        ring
      rw [Finset.prod_congr rfl (fun v _ => hterm v), NNReal.finsetProd_rpow]
      have h := congrArg (fun n : ℕ => (n : ℝ≥0)) (prod_absNorm_pow_count_differentIdeal_eq_natAbs_discr F)
      simp only [Nat.cast_prod, Nat.cast_pow] at h
      rw [h]
      have ha0 : ((discr F).natAbs : ℝ≥0) ≠ 0 := by
        exact_mod_cast Int.natAbs_ne_zero.2 (discr_ne_zero F)
      have ha : (((discr F).natAbs : ℝ≥0) : ℝ) = |(discr F : ℝ)| := by
        rw [NNReal.coe_natCast, Nat.cast_natAbs, Int.cast_abs]
      rw [← ha, ← Real.coe_sqrt, Real.toNNReal_coe, NNReal.sqrt_eq_rpow, ← NNReal.rpow_add ha0]
      norm_num
    · intro v hv
      rw [Function.mem_mulSupport] at hv
      rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hv (by rw [h0]; simp)

end GlobalTheory.CompanionTheory.SW.SelfDual
