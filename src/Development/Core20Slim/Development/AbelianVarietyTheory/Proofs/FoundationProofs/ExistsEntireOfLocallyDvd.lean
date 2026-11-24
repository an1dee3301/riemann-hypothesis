module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

namespace GlobalTheory.EvenTheta

theorem exists_entire_of_locally_dvd {F S : ℂ → ℂ} (hS : Dense {z | S z ≠ 0})
    (h : ∀ w, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ ∀ᶠ z in 𝓝 w, F z = S z * g z) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = S z * G z := by
  choose g hg hF using h
  refine ⟨fun w => g w w, fun w => ?_, fun z => (hF z).self_of_nhds⟩
  refine (hg w).differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [(hg w).eventually_analyticAt, (hF w).eventually_nhds] with z h1 h2
  refine tendsto_nhds_unique_of_frequently_eq (hg z).continuousAt h1.continuousAt ?_
  have h3 : ∃ᶠ y in 𝓝 z, S y ≠ 0 := mem_closure_iff_frequently.1 (hS z)
  refine (h3.and_eventually (h2.and (hF z))).mono fun y hy => ?_
  exact mul_left_cancel₀ hy.1 (hy.2.2.symm.trans hy.2.1)

theorem IsLat.exists_sg_add {Λ : AddSubgroup ℂ} (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) :
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ z, sgStar Λ (z + ω) = c z * sgStar Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.sgStar_eq L Λ hL]
  refine ⟨_, ?_, GlobalTheory.canonicalSigma_add L ((hL ω).1 hω)⟩
  unfold GlobalTheory.latticeForm
  fun_prop

theorem exists_eq_sg_sq_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 0 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * (k + 1)) = F z * sgStar Λ (z + ω) ^ (2 * (k + 1))) → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (-z) = G z) ∧ (∀ z, F z = sgStar Λ z ^ 2 * G z) ∧ ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ (2 * k) = G z * sgStar Λ (z + ω) ^ (2 * k) := by
  intro Λ hΛ k F hF he h0 hlaw
  have hσ := hΛ.differentiable
  have hσc := hσ.continuous
  have hFc := hF.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (hΛ.sg_eq_zero z).not.2 hz
  obtain ⟨h, hh, eh⟩ := GlobalTheory.exists_eq_add_sq_mul_of_even (hF.analyticAt 0) he
  have hu : AnalyticAt ℂ (dslope (sgStar Λ) 0) 0 :=
    (differentiableOn_univ.1
      ((Complex.differentiableOn_dslope univ_mem).2 hσ.differentiableOn)).analyticAt 0
  have hu0 : dslope (sgStar Λ) 0 0 ≠ 0 := by
    rw [dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1]
    exact one_ne_zero
  have eu : ∀ z, sgStar Λ z = z * dslope (sgStar Λ) 0 z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(hΛ.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  obtain ⟨G, hG, eG⟩ := exists_entire_of_locally_dvd (F := F) (S := fun z => sgStar Λ z ^ 2)
    (hΛ.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => by
      by_cases hw : w ∈ Λ
      · obtain ⟨c, hc, ec⟩ := hΛ.exists_sg_add hw
        have hcc := hc.continuous
        have eF : ∀ z, F (z + w) = c z ^ (2 * (k + 1)) * F z := fun z => by
          refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => F (z + w))
            (g := fun z => c z ^ (2 * (k + 1)) * F z) (by fun_prop) (by fun_prop) fun z hz => ?_) z
          refine mul_right_cancel₀ (pow_ne_zero (2 * (k + 1)) (hne z hz)) ?_
          beta_reduce
          rw [hlaw w hw, ec]
          ring
        have hs : AnalyticAt ℂ (fun y : ℂ => y - w) w := by fun_prop
        have ha : AnalyticAt ℂ
            (fun z => c z ^ (2 * k) * h z / dslope (sgStar Λ) 0 z ^ 2) 0 :=
          (((hc.analyticAt 0).pow _).mul hh).div (hu.pow 2) (pow_ne_zero 2 hu0)
        refine ⟨_, ha.comp_of_eq hs (sub_self w), ?_⟩
        filter_upwards [(hu.comp_of_eq hs (sub_self w)).continuousAt.eventually_ne
          (y := 0) (by simpa using hu0)] with y hy
        obtain ⟨z, rfl⟩ : ∃ z, y = z + w := ⟨y - w, by ring⟩
        simp only [Function.comp, add_sub_cancel_right] at hy ⊢
        rw [eF, ec, eh, h0, eu z]
        field_simp
        ring
      · refine ⟨fun z => F z / sgStar Λ z ^ 2, (hF.analyticAt w).div ((hσ.analyticAt w).pow 2)
          (pow_ne_zero 2 (hne w hw)), ?_⟩
        filter_upwards [hσc.continuousAt.eventually_ne (hne w hw)] with y hy
        field_simp
  have hGc := hG.continuous
  refine ⟨G, hG, fun z => ?_, eG, fun ω hω z => ?_⟩
  · refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [he, hΛ.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  · refine congrFun (Continuous.ext_on hΛ.dense_compl
      (f := fun z => G (z + ω) * sgStar Λ z ^ (2 * k))
      (g := fun z => G z * sgStar Λ (z + ω) ^ (2 * k)) (by fun_prop) (by fun_prop)
      fun z hz => ?_) z
    have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using Λ.sub_mem h' hω)
    refine mul_left_cancel₀
      (mul_ne_zero (pow_ne_zero 2 (hne z hz)) (pow_ne_zero 2 (hne _ hz'))) ?_
    have h1 := hlaw ω hω z
    rw [eG z, eG (z + ω)] at h1
    beta_reduce at h1 ⊢
    linear_combination h1

end GlobalTheory.EvenTheta
