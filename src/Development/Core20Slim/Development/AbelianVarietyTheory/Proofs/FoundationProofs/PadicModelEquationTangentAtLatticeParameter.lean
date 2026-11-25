module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
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
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.ModelPoint

theorem wpD_sq {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    wpD Λ v ^ 2 = 4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ := by
  obtain ⟨w₁, w₂, hi, hΛ⟩ := h
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  rw [GlobalTheory.LatticeInvariants.wpD_eq hL, GlobalTheory.LatticeInvariants.wpF_eq hL,
    GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
  exact L.derivWeierstrassP_sq v fun h => hv ((hL v).2 h)

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := dif_pos x.2

theorem lamC_neg_div_four (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) :
    lamC lam (-x / 4) = -lamC lam x / 4 := by
  lift x to Qbar using hx
  have e : (-(x : ℂ) / 4) = ((-x / 4 : Qbar) : ℂ) := by push_cast; rfl
  rw [e, lamC_coe, lamC_coe, map_div₀, map_neg, map_ofNat]

theorem lamC_eqn (lam : Qbar →+* ℂ_[p]) {x y a b : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (h : y ^ 2 = 4 * x ^ 3 - a * x - b) :
    lamC lam y ^ 2 = 4 * lamC lam x ^ 3 - lamC lam a * lamC lam x - lamC lam b := by
  lift x to Qbar using hx
  lift y to Qbar using hy
  lift a to Qbar using ha
  lift b to Qbar using hb
  have e : y ^ 2 = 4 * x ^ 3 - a * x - b := by
    apply Subtype.ext
    push_cast
    exact h
  have := congrArg lam e
  simpa only [lamC_coe, map_sub, map_mul, map_pow, map_ofNat] using this

theorem model_point : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  intro p _ g v hL h2 h3 hv hx hy
  have key := lamC_eqn g.lam hx hy h2 h3 (wpD_sq hL hv)
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt,
      lamC_neg_div_four g.lam h2, lamC_neg_div_four g.lam h3]
    linear_combination ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 / 4 * key
  · simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₃, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt]
    ring

end GlobalTheory.ThetaPar.ModelPoint
