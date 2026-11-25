module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
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
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}

def sqTh (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ (v + z) * sgStar Λ (v - z) / sgStar Λ v ^ 2

def AlgEnt (F : ℂ → ℂ) : Prop := Differentiable ℂ F ∧ ∀ n, coef1 F n ∈ Qbar

def IntSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop := ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1

def BddSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop :=
  ∃ B : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ B

def lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) : PowerSeries K :=
  e - PowerSeries.C x * PowerSeries.X ^ 2

def IsWpSer {K : Type*} [CommRing K] (a b : K) (P : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff P = 1 ∧
    (PowerSeries.X * PowerSeries.derivativeFun P - 2 * P) ^ 2 =
      4 * P ^ 3 - PowerSeries.C a * PowerSeries.X ^ 4 * P - PowerSeries.C b * PowerSeries.X ^ 6

def xAt {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lamC g.lam (wpF g.abelian₂ v) - g.C.r)

variable {Λ : AddSubgroup ℂ}

theorem IsLat.differentiable (h : IsLat Λ) : Differentiable ℂ (sgStar Λ) :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.1

theorem IsLat.sg_neg (h : IsLat Λ) (z : ℂ) : sgStar Λ (-z) = -sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.1 z

theorem IsLat.sg_eq_zero (h : IsLat Λ) (z : ℂ) : sgStar Λ z = 0 ↔ z ∈ Λ :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).2.1 z

theorem IsLat.sg_law (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω z

theorem IsLat.dense_compl (h : IsLat Λ) : Dense (Λ : Set ℂ)ᶜ := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun z => hL z
  rw [this]
  exact GlobalTheory.dense_compl_lattice L

theorem IsLat.differentiable_sqTh (h : IsLat Λ) (v : ℂ) : Differentiable ℂ (sqTh Λ v) := by
  have := h.differentiable
  unfold sqTh
  fun_prop

theorem sqTh_neg (v z : ℂ) : sqTh Λ v (-z) = sqTh Λ v z := by
  simp only [sqTh, sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

theorem IsLat.sqTh_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) : sqTh Λ v 0 = 1 := by
  have := (h.sg_eq_zero v).not.2 hv
  simp only [sqTh, add_zero, sub_zero]
  field_simp

theorem IsLat.sqTh_eq_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    sqTh Λ v z = 0 ↔ v + z ∈ Λ ∨ v - z ∈ Λ := by
  have := (h.sg_eq_zero v).not.2 hv
  simp [sqTh, this, h.sg_eq_zero]

theorem IsLat.sqTh_eq (h : IsLat Λ) {v z : ℂ} (hv : v ∉ Λ) (hz : z ∉ Λ) :
    sqTh Λ v z = sgStar Λ z ^ 2 * (wpF Λ z - wpF Λ v) := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have h1 := (GlobalTheory.OddTheta.sgStar_laws Λ h).2.2.2.1 v z hv hz
  rw [sqTh, div_eq_iff (pow_ne_zero 2 h0)]
  linear_combination h1

theorem IsLat.sqTh_sub (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) (z : ℂ) :
    sqTh Λ v z = sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2 := by
  have h1 := (h.differentiable_sqTh v).continuous
  have h2 := (h.differentiable_sqTh w).continuous
  have h3 := h.differentiable.continuous
  refine congrFun (Continuous.ext_on h.dense_compl h1
    (g := fun z => sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2) (by fun_prop) fun z hz => ?_) z
  beta_reduce
  rw [h.sqTh_eq hv hz, h.sqTh_eq hw hz]
  ring

theorem IsLat.wp_eq_iff (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) :
    wpF Λ w = wpF Λ v ↔ v + w ∈ Λ ∨ v - w ∈ Λ := by
  rw [← h.sqTh_eq_zero hv, h.sqTh_eq hv hw]
  simp [(h.sg_eq_zero w).not.2 hw, sub_eq_zero]

theorem IsLat.sqTh_mul (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    (U1 Λ v (sgStar Λ) 0 * U1 Λ (-v) (sgStar Λ) 0) * sqTh Λ v z =
      U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have e : ∀ z : ℂ, U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z =
      -(sgStar Λ (v + z) * sgStar Λ (v - z)) *
        Complex.exp (-((Real.pi : ℂ) * v * (starRingEnd ℂ) v / (area Λ : ℂ))) := by
    intro z
    simp only [U1]
    rw [show z + -v = -(v - z) by ring, h.sg_neg, add_comm z v, mul_mul_mul_comm, ← Complex.exp_add]
    congr 1
    · ring
    · congr 1
      simp only [map_neg]
      ring
  rw [e, e, sqTh]
  simp only [add_zero, sub_zero]
  field_simp

end GlobalTheory.EvenTheta
