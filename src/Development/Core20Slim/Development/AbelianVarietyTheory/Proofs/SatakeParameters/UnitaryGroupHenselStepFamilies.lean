module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralDualOfIndependentModUniformizerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformIntegralUnitaryCongruentOneStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3.IntWitt

theorem hensel_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L) (k : ℕ), 1 ≤ k →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    (∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k (z' i r - z i r)) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hherm ι _ z z' k hk hz hz' hind hdiff hgram
  classical
  have hv := hU.2.2.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hσv := hU.2.1
  have hϖI : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv]; exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 from by decide)
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJI : ∀ r s, J r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hJiI : ∀ r s, Ji r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  choose w hwI hwe using hdiff
  have hz'e : ∀ i r, z' i r = z i r + ϖ ^ k * w i r := fun i r => by rw [← hwe]; ring
  have hz'v : ∀ i, z' i = z i + ϖ ^ k • w i := fun i => funext fun r => by simp [hz'e]

  have hformI : ∀ x y : Fin n' → L, (∀ r, x r ∈ Formalism.UG.intL L) → (∀ r, y r ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ J x y ∈ Formalism.UG.intL L := by
    intro x y hx hy
    refine sum_mem fun r _ => sum_mem fun s _ => mul_mem (mul_mem ?_ (hJI r s)) (hy s)
    show Valued.v (σ (x r)) ≤ 1
    rw [hσv]; exact hx r
  have key : ∀ i j, Formalism.UG.hform σ J (z' i) (z' j) - Formalism.UG.hform σ J (z i) (z j) =
      ϖ ^ k * (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) + ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
    intro i j
    simp only [Formalism.UG.hform, hz'e, map_add (f := _), map_mul, map_pow, hσϖ, mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  have hgram1 : ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j)) := by
    intro i j
    have h1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) +
        ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      obtain ⟨b, hb, hbe⟩ := hgram i j
      refine ⟨b, hb, ?_⟩
      have := (key i j).symm.trans hbe
      rw [pow_succ, mul_assoc] at this
      rw [pow_one]
      exact mul_left_cancel₀ (pow_ne_zero k hϖ0) this
    have h2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      refine ⟨ϖ ^ (k - 1) * Formalism.UG.hform σ J (w i) (w j),
        mul_mem (pow_mem hϖI _) (hformI _ _ (hwI i) (hwI j)), ?_⟩
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    have := GlobalTheory.Hk3.IntWitt.dvdPow_sub h1 h2
    simpa using this
  obtain ⟨a, haI, ha⟩ := GlobalTheory.T.exists_integral_dual_of_independentModUniformizer L ϖ hv n' ι z hz hind
  obtain ⟨C, hCs, hCI, hCz⟩ := GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer L ϖ σ q hU hq n' JT hJT hherm ι z w a hz hwI haI ha hgram1
  obtain ⟨g, hgI, hg1, hg2⟩ := GlobalTheory.T.cayley_transform_integral_unitary_congruent_one L ϖ σ q hU hq n' JT hJT hherm C hCs hCI k hk
  refine ⟨g, hgI, hg1, fun i r => ?_⟩
  set G : Matrix (Fin n') (Fin n') L := ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hGdef
  have e : G *ᵥ z i - z' i = (G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i + ϖ ^ k • (Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec (w i) Ji J, hJiJ, Matrix.one_mulVec, hz'v, smul_sub]
    abel
  have e' := congrFun e r
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e'
  rw [e']
  have t1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (((G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (∑ s, (G - 1 - ϖ ^ k • (Ji * C)) r s * z i s)
    refine GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => ?_
    rw [mul_comm]
    exact GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hg2 r s) (hz i s)
  have t2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (∑ s, Ji r s * (C *ᵥ z i - J *ᵥ w i) s)
    exact GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hCz i s) (hJiI r s)
  refine GlobalTheory.Hk3.IntWitt.dvdPow_add t1 ?_
  obtain ⟨b, hb, hbe⟩ := t2
  exact ⟨b, hb, by rw [hbe, pow_succ]; ring⟩

end GlobalTheory.Hk3.IntWitt
