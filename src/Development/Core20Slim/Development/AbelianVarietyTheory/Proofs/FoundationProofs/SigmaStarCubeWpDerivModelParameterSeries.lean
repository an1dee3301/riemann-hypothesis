module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplex
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Cast
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
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
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
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
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
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
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

namespace GlobalTheory.FrobStick

open PowerSeries

theorem omegaW_mul_inv {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (hwq : IsWq W wq) :
    omegaW W wq * (wq⁻¹ * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) =
      X * derivative (R := ℂ_[p]) wq⁻¹ - 2 * wq⁻¹ ∧ omegaW W wq ≠ 0 := by
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative (R := ℂ_[p]) wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * derivative (R := ℂ_[p]) wq) * (wq * N)⁻¹ := by
      have hd : dX wq = derivative (R := ℂ_[p]) wq := by
        ext n
        simp [dX, coeff_derivative, mul_comm]
      unfold omegaW
      rw [hd]
      rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * derivative (R := ℂ_[p]) e + e * derivative (R := ℂ_[p]) wq = 0 := by
    have := congrArg (derivative (R := ℂ_[p])) he
    rw [Derivation.leibniz] at this
    simpa using this
  have key : omegaW W wq * (e * N) = X * derivative (R := ℂ_[p]) e - 2 * e := by
    linear_combination e ^ 2 * hω - X * e * hde -
      (omegaW W wq * N * e + 2 * e - X * derivative (R := ℂ_[p]) e) * he
  refine ⟨key, fun h => ?_⟩
  rw [h, zero_mul] at key
  have := congrArg constantCoeff key
  simp [he1, h2] at this

theorem atU_sgStar_eq {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (X * ePhi1 g.lam g.abelian₂ g.C g.wq) := by
  have h0 : constantCoeff (GL3Theta.ser1 g.lam (sgStar g.abelian₂)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.taylorCoeff_zero_eq_value,
      (hL.sg_eq_zero 0).2 (zero_mem _)]
    exact (GlobalTheory.SerTransport.lamC_coe g.lam 0).trans (map_zero g.lam)
  obtain ⟨S, hS⟩ := X_dvd_iff.2 h0
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g S hS, GlobalTheory.SerTransport.atU_eq, hS, subst_mul hs, subst_X hs,
    mul_assoc]

theorem colC_atU : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  intro hD p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hQ, eQ⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hσ', dσ⟩ := hD p g _ hσ
  obtain ⟨hQ', dQ⟩ := hD p g _ hQ
  obtain ⟨hT, hc, -⟩ := GlobalTheory.SerTransport.transport p g
  have hm : (-2 : ℂ) ∈ Qbar := neg_mem (ofNat_mem _ 2)
  obtain ⟨c1, c2⟩ := hc _ hm
  have c3 : lamC g.lam (-2) = -2 := by
    have : (-2 : ℂ) = ((-2 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  obtain ⟨a1, a2⟩ := (hT _ _ hσ hQ').1
  obtain ⟨b1, b2⟩ := (hT _ _ c1 hσ').1
  obtain ⟨d1, d2⟩ := (hT _ _ b1 hQ).1
  obtain ⟨f1, f2⟩ := (hT _ _ a1 d1).2
  have e : colC g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (-2 * deriv (sgStar g.abelian₂) z) * sqTh g.abelian₂ v z := by
    funext z
    rw [colC]; ring
  rw [e]
  refine ⟨f1, ?_⟩
  rw [f2, a2, d2, b2, c2, c3, map_neg, map_ofNat]
  obtain ⟨hω, hω0⟩ := omegaW_mul_inv g.W g.wq hq
  have eS := atU_sgStar_eq g hL
  have hε : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    rw [constantCoeff_C, map_zero] at this
    exact Units.ne_zero _ this
  apply mul_left_cancel₀ (mul_ne_zero hε hω0)
  rw [eQ, lineSer] at dQ
  rw [eS] at dσ
  rw [eQ, eS, lineSer]
  generalize ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ε at *
  generalize ePhi1 g.lam g.abelian₂ g.C g.wq = E at *
  generalize g.wq⁻¹ = q at *
  generalize xAt g v = x at *
  have k1 : derivative (R := ℂ_[p]) (C ε * (X * E)) = C ε * (E + X * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, Derivation.leibniz]; simp [add_comm]
  have k2 : derivative (R := ℂ_[p]) (E ^ 2 * (q - C x * X ^ 2)) =
      E ^ 2 * (derivative (R := ℂ_[p]) q - C x * (2 * X)) + (q - C x * X ^ 2) * (2 * E * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, map_sub, Derivation.leibniz (a := C x), Derivation.leibniz_pow, Derivation.leibniz_pow]
    simp only [derivative_C, derivative_X, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [k1] at dσ
  rw [k2] at dQ
  linear_combination -(C ε * (X * E)) * dQ + 2 * (E ^ 2 * (q - C x * X ^ 2)) * dσ - C ε * E ^ 3 * hω

end GlobalTheory.FrobStick
