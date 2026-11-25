module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
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
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GenusOneDatum


open PowerSeries in
theorem exists_fixed_of_contract {R : Type*} [CommRing R] (T : PowerSeries R → PowerSeries R)
    (hT : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ x - y → X ^ (n + 1) ∣ T x - T y) :
    ∃ x, T x = x := by
  have hit : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ T^[n] x - T^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y)
  let L : PowerSeries R := PowerSeries.mk fun n => coeff n (T^[n + 1] 0)
  have hL : ∀ n, X ^ n ∣ L - T^[n] 0 := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, n = (m + 1) + k := ⟨n - (m + 1), by omega⟩
    have := X_pow_dvd_iff.1 (hit (m + 1) 0 (T^[k] 0)) m (by omega)
    rw [← Function.iterate_add_apply] at this
    simpa [L] using this
  refine ⟨L, ?_⟩
  ext n
  have h1 := hT n _ _ (hL n)
  have h2 := hL (n + 1)
  rw [Function.iterate_succ_apply'] at h2
  have h3 := dvd_sub h1 h2
  have h4 := X_pow_dvd_iff.1 h3 n (by omega)
  rw [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h4
  exact h4

theorem exists_isWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) : ∃ wq, IsWq W wq := by
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  obtain ⟨w, hw⟩ := exists_fixed_of_contract (fun wq : PowerSeries ℂ_[p] =>
    1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3) (by
      rintro n x y ⟨z, hz⟩
      refine ⟨z * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2)), ?_⟩
      have hz' : x - y = X ^ n * z := hz
      change _ = X ^ (n + 1) * _
      linear_combination (X * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2))) * hz')
  exact ⟨w, hw.symm⟩

theorem constantCoeff_of_isWq {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.constantCoeff wq = 1 := by
  have h' := congrArg PowerSeries.constantCoeff h
  simpa using h'

theorem coeff_one_flog {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  simp [flog, omegaW, PowerSeries.constantCoeff_inv, constantCoeff_of_isWq h, h2]

theorem constantCoeff_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (flog W wq) = 0 := by
  simp [flog]

theorem exists_subst_eq_X {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    ∃ ex : PowerSeries R, PowerSeries.constantCoeff ex = 0 ∧
      PowerSeries.subst ex l = PowerSeries.X := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, -⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h ()⟩

theorem exists_genusOne_datum : ∀ (D : D7), GL3Theta.modelEx D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∃ g : GL3Theta.G1 p, GL3Theta.At D cc δ g ∧ g.lam = lam ∧ ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  intro D hm p _ lam cc δ hc hcop
  obtain ⟨⟨C, hC⟩, -, hu⟩ := hm p lam cc δ hc.1 hcop hc.2
  obtain ⟨wq, hwq⟩ := exists_isWq (C • wModel lam (lamOf D cc δ))
  obtain ⟨ex, he0, he⟩ := exists_subst_eq_X _ (constantCoeff_flog _ wq) (coeff_one_flog hwq)
  exact ⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, ⟨hc.1, hcop, hc.2, rfl, hC, hwq, he0, he⟩, rfl, hu C hC⟩

end GlobalTheory.GenusOneDatum
