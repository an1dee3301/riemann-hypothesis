module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.DatumBasic

variable {p : ℕ} [Fact p.Prime]

theorem wModel_Δ (lam : Qbar →+* ℂ_[p]) {Λ : AddSubgroup ℂ} (h2 : g2 Λ ∈ Qbar) (h3 : g3 Λ ∈ Qbar)
    (hd : TaylorLogMetric.discr Λ = 1) : (wModel lam Λ).Δ = 1 := by
  set a : Qbar := ⟨g2 Λ, h2⟩ with ha
  set b : Qbar := ⟨g3 Λ, h3⟩ with hb
  have hc : ∀ x : Qbar, lamC lam (-(x : ℂ) / 4) = -(lam x) / 4 := by
    intro x
    have e : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast
      rfl
    rw [e, lamC, dite_eq_left (-x / 4).2]
    change lam (-x / 4) = _
    rw [map_div₀, map_neg, map_ofNat]
  have e : a ^ 3 - 27 * b ^ 2 = 1 := by
    apply Subtype.ext
    push_cast
    exact hd
  have e2 := congrArg lam e
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one] at e2
  have ea := hc a
  have eb := hc b
  simp only [ha, hb] at ea eb
  simp only [wModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ea, eb]
  linear_combination e2

theorem intSer_of_isWq {W : WeierstrassCurve ℂ_[p]} (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) {w : PowerSeries ℂ_[p]}
    (h : IsWq W w) : IntSer w := by
  obtain ⟨hr, -, hC, hX, -⟩ := SerRing.series_ring_laws p
  have hadd : ∀ {f g : PowerSeries ℂ_[p]}, IntSer f → IntSer g → IntSer (f + g) :=
    fun hf hg => (hr _ _ hf hg).1
  have hterm : ∀ (c : ℂ_[p]) (i j : ℕ) (t : PowerSeries ℂ_[p]), ‖c‖ ≤ 1 → IntSer t →
      IntSer (PowerSeries.C c * PowerSeries.X ^ i * t ^ j) := fun c i j t hc ht =>
    SerRing.intSer_mul (SerRing.intSer_mul ((hC c).2 hc) (SerRing.intSer_pow hX i))
      (SerRing.intSer_pow ht j)
  have hone : IntSer (1 : PowerSeries ℂ_[p]) := by simpa using SerRing.intSer_pow hX 0
  have key : ∀ n : ℕ, ∃ t : PowerSeries ℂ_[p], IntSer t ∧ PowerSeries.X ^ n ∣ w - t := by
    intro n
    induction n with
    | zero => exact ⟨1, hone, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, z, hz⟩ := ih
      refine ⟨_, hadd (hadd (hadd (hadd (hadd hone (hterm _ 1 1 t h1 ht)) (hterm _ 2 1 t h2 ht))
        (hterm _ 3 2 t h3 ht)) (hterm _ 4 2 t h4 ht)) (hterm _ 6 3 t h6 ht),
        z * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2)), ?_⟩
      have h' : w = 1 + PowerSeries.C W.a₁ * PowerSeries.X * w +
          PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C W.a₃ * PowerSeries.X ^ 3 * w ^ 2 +
          PowerSeries.C W.a₄ * PowerSeries.X ^ 4 * w ^ 2 +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 6 * w ^ 3 := h
      linear_combination h' + (PowerSeries.X * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2))) * hz
  intro n
  obtain ⟨t, ht, hd⟩ := key (n + 1)
  have e := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at e
  rw [e]
  exact ht n

theorem datum_basic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → ‖((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ IntSer g.wq⁻¹ ∧ PowerSeries.constantCoeff g.wq⁻¹ = 1 ∧ PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  intro p _ g ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hw, _⟩ hL a2 a3 hd
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have := congrArg PowerSeries.constantCoeff hw
    simpa using this
  refine ⟨?_, SerRing.intSer_inv (intSer_of_isWq h1 h2 h3 h4 h6 hw) (by rw [hw0, norm_one]),
    by rw [PowerSeries.constantCoeff_inv, hw0, inv_one],
    GlobalTheory.ThetaParam.constantCoeff_ePhi1 g hw (GlobalTheory.OddTheta.sgStar_laws _ hL).1.2.1,
    GlobalTheory.ThetaParam.atU_sg g ((hL.sg_eq_zero 0).2 (zero_mem _))⟩
  rw [WeierstrassCurve.variableChange_Δ, wModel_Δ g.lam a2 a3 hd, mul_one, norm_pow] at hΔ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hΔ

end GlobalTheory.EvenTheta.DatumBasic
