module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarAdditionFormulaPadicModelParameter
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory


open Formalism.MainNotions.GL3Theta in
theorem mulBy_integral_isClosed : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsClosed {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} := by
  intro p _ g
  set L : MvPowerSeries Unit ℂ_[p] := g.lg (GL3Theta.Xv ()) with hLdef
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by
    rw [hLdef, GL3Theta.G1.lg]
    exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _
      (GlobalTheory.GenusOneDatum.constantCoeff_flog _ _)
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have key : ∀ e : Unit →₀ ℕ, ∃ S : Finset ℕ, ∀ c : ℂ_[p],
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
        ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
    intro e
    have hfin := PowerSeries.coeff_subst_finite hL (PowerSeries.mk fun _ => (1 : ℂ_[p])) e
    have hfin' : (Function.support fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.mk fun _ => (1 : ℂ_[p])) • MvPowerSeries.coeff e (L ^ d)).Finite := hfin
    refine ⟨hfin'.toFinset, fun c => ?_⟩
    have ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * L) = 0 := by
      simp [hL0]
    have ha : PowerSeries.HasSubst (MvPowerSeries.C c * L) :=
      PowerSeries.HasSubst.of_constantCoeff_zero ha0
    show MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.C c * L) g.ex) = _
    rw [PowerSeries.coeff_subst ha]
    have hterm : ∀ d : ℕ, PowerSeries.coeff d g.ex • MvPowerSeries.coeff e ((MvPowerSeries.C c * L) ^ d) =
        PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
      intro d
      rw [mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, smul_eq_mul]
    simp_rw [hterm]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hd
    simp only [PowerSeries.coeff_mk, one_smul] at h0
    rw [h0, mul_zero, mul_zero]
  have hset : {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} =
      ⋂ e : Unit →₀ ℕ, {c : ℂ_[p] |
        ‖MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])‖ ≤ 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [hset]
  refine isClosed_iInter fun e => ?_
  obtain ⟨S, hS⟩ := key e
  have hfun : (fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])) =
      fun c => ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) :=
    funext hS
  have hcont : Continuous fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    rw [hfun]
    fun_prop
  exact isClosed_le (continuous_norm.comp hcont) continuous_const

end GlobalTheory
