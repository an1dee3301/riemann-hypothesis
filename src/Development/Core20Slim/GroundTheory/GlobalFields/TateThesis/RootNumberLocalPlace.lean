module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.Core20Slim.GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.FiniteAdeleDecomp
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
public import GroundTheory.LocalFields.LocalFourierChar
public import GroundTheory.LocalFields.LocalFourierHaar
public import Development.Core20Slim.GroundTheory.LocalFields.LocalZetaShell
public import GroundTheory.LocalFields.PadicLogSeries
public import GroundTheory.LocalFields.UnitsBasic
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
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory WithZero
  GroundTheory.LocalField IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar continuous_localChar)
open scoped NumberField.AdeleRing ENNReal NNReal

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Valuation

variable {v : HeightOneSpectrum (𝓞 K)}

theorem residueCard_adicCompletion : residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal :=
  natCard_residueField_adicCompletion v

theorem valued_eq_exp_neg_ord {x : v.adicCompletion K} (hx : x ≠ 0) :
    Valued.v x = exp (-ord x) := by
  have h1 := norm_eq_absNorm_zpow_neg_ord v hx
  have h2 := normalizedAbv_eq_zpow v hx
  rw [normalizedAbv_apply] at h2
  have hN : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    rw [← residueCard_adicCompletion]
    exact_mod_cast one_lt_residueCard (K := v.adicCompletion K)
  have h := zpow_right_injective₀ (a := (Ideal.absNorm v.asIdeal : ℝ)) (by linarith) hN.ne'
    (h2.symm.trans h1)
  rw [← exp_log ((Valued.v).ne_zero_iff.2 hx)]
  exact congrArg exp h

theorem mem_valBall_iff_valued {n : ℤ} {x : v.adicCompletion K} :
    x ∈ valBall (v.adicCompletion K) n ↔ Valued.v x ≤ exp (-n) := by
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, zero_le, iff_true]
    exact zero_mem _
  · rw [mem_valBall_iff_le_ord hx, valued_eq_exp_neg_ord hx, exp_le_exp]
    omega


end Valuation

section AddChar

variable (v : HeightOneSpectrum (𝓞 K))

theorem isTrivialOn_localAdelicChar_iff (n : ℤ) :
    IsTrivialOn (localAdelicChar K v) n ↔ -differentExp v ≤ n := by
  have hM : ∀ a ∈ v.adicCompletionIntegers K, ∀ x ∈ valBall (v.adicCompletion K) n,
      a * x ∈ valBall (v.adicCompletion K) n := by
    intro a ha x hx
    rw [mem_valBall_iff_valued] at hx ⊢
    rw [map_mul]
    calc Valued.v a * Valued.v x ≤ 1 * Valued.v x := by
          gcongr
          exact (mem_adicCompletionIntegers _ _ _).1 ha
      _ = Valued.v x := one_mul _
      _ ≤ exp (-n) := hx
  change (∀ x ∈ valBall (v.adicCompletion K) n, localAdelicChar K v x = 1) ↔ _
  rw [forall_localAdelicChar_eq_one_iff_le v _ hM]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hx : ((unifUnit (v.adicCompletion K) ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
        valBall (v.adicCompletion K) n := by
      rw [mem_valBall_iff_le_ord (Units.ne_zero _), ord_unifUnit_zpow]
    have h2 := (mem_localInvDifferent_iff_valued v _).1 (h hx)
    rw [valued_eq_exp_neg_ord (Units.ne_zero _), ord_unifUnit_zpow, exp_le_exp] at h2
    change -n ≤ differentExp v at h2
    omega
  · intro h x hx
    rw [mem_localInvDifferent_iff_valued]
    exact ((mem_valBall_iff_valued).1 hx).trans (exp_le_exp.2 (by change -n ≤ differentExp v; omega))

theorem localAdelicChar_ne_one : localAdelicChar K v ≠ 1 := by
  intro h
  have h1 : IsTrivialOn (localAdelicChar K v) (-differentExp v - 1) := fun x _ ↦ by
    rw [h]
    rfl
  have := (isTrivialOn_localAdelicChar_iff v _).1 h1
  omega

theorem addCharConductor_localAdelicChar :
    addCharConductor (localAdelicChar K v) = -differentExp v := by
  have hc := continuous_localAdelicChar v
  have hne := localAdelicChar_ne_one v
  apply le_antisymm
  · exact (isTrivialOn_iff hc hne _).1 ((isTrivialOn_localAdelicChar_iff v _).2 le_rfl)
  · exact (isTrivialOn_localAdelicChar_iff v _).1 (isTrivialOn_addCharConductor hc hne)

end AddChar

namespace HeckeCharacter

variable (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))











end HeckeCharacter

end

end GroundTheory.Global
