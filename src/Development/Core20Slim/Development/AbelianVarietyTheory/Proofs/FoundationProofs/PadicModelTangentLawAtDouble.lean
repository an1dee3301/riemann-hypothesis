module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
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
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
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
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
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
public import Mathlib.Data.Subtype
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
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
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ModelDouble

open WeierstrassCurve

theorem weierstrassP_two_mul (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) (h2 : 2 * P ∉ L.lattice) :
    L.derivWeierstrassP P ≠ 0 ∧
      L.weierstrassP (2 * P) =
        ((3 * L.weierstrassP P ^ 2 - L.g₂ / 4) / L.derivWeierstrassP P) ^ 2 - 2 * L.weierstrassP P := by
  have hPP : P + P ∉ L.lattice := by rwa [← two_mul]
  have hd : L.derivWeierstrassP P ≠ 0 := (GlobalTheory.derivWeierstrassP_eq_zero_iff L hP).not.mpr hPP
  refine ⟨hd, ?_⟩
  have h := GlobalTheory.latticePoint_add L P P
  have hy : L.derivWeierstrassP P / 2 ≠
      (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP P) (L.derivWeierstrassP P / 2) := by
    simp only [Affine.negY, GlobalTheory.latticeCurve]
    intro e; apply hd; linear_combination e
  rw [GlobalTheory.latticePoint_of_notMem L hP, GlobalTheory.latticePoint_of_notMem L hPP,
    Affine.Point.add_of_Y_ne hy, Affine.Point.some.injEq] at h
  rw [two_mul, h.1, Affine.slope_of_Y_ne rfl hy]
  simp only [Affine.addX, Affine.negY, GlobalTheory.latticeCurve]
  rw [show L.derivWeierstrassP P / 2 - (-(L.derivWeierstrassP P / 2) - 0 * L.weierstrassP P - 0) = L.derivWeierstrassP P by ring]
  field_simp
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : Qbar} (hx : x ≠ 0) : lam x ≠ 0 :=
  (map_ne_zero lam).mpr hx

theorem tangent_law : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → 2 * P ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → 2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃ ≠ 0 ∧ GlobalTheory.EvenTheta.xAt g (2 * P) = ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) ^ 2 + g.W.a₁ * ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) - g.W.a₂ - 2 * GlobalTheory.EvenTheta.xAt g P := by
  intro p _ g P hlat hg2 _ hP h2P hwF hwD
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair _ hlat
  obtain ⟨hd, hdup⟩ := weierstrassP_two_mul L ((hL P).not.mp hP) ((hL _).not.mp h2P)
  simp only [← GlobalTheory.LatticeInvariants.wpF_eq hL, ← GlobalTheory.LatticeInvariants.wpD_eq hL,
    ← GlobalTheory.LatticeInvariants.g2_eq hL] at hd hdup
  set a : Qbar := ⟨wpF g.abelian₂ P, hwF⟩ with ha
  set d : Qbar := ⟨wpD g.abelian₂ P, hwD⟩ with hd'
  set G : Qbar := ⟨g2 g.abelian₂, hg2⟩ with hG
  have hd0 : d ≠ 0 := fun h => hd (congrArg Subtype.val h)
  have he : wpF g.abelian₂ (2 * P) = (((((3 * a ^ 2 - G / 4) / d) ^ 2 - 2 * a : Qbar)) : ℂ) := by
    rw [hdup]; simp [a, d, G]; norm_cast
  have lX : lamC g.lam (wpF g.abelian₂ P) = g.lam a := lamC_coe _ a
  have lD : lamC g.lam (wpD g.abelian₂ P) = g.lam d := lamC_coe _ d
  have l2 : lamC g.lam (wpF g.abelian₂ (2 * P)) = ((3 * g.lam a ^ 2 - g.lam G / 4) / g.lam d) ^ 2 - 2 * g.lam a := by
    rw [he, lamC_coe]; simp [map_div₀, map_ofNat]
  have lA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam G) / 4 := by
    rw [show -(g2 g.abelian₂) / 4 = ((-G / 4 : Qbar) : ℂ) by simp [G]; norm_cast, lamC_coe]; simp [map_div₀, map_ofNat]
  have lD0 : g.lam d ≠ 0 := lamC_ne_zero _ hd0
  have ε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  simp only [GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt, GL3Theta.G1.W, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, wModel, lX, lD, l2, lA]
  set ε := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
  set X := g.lam a
  set D := g.lam d
  have hden : 2 * (ε ^ 3 * (D / 2 - g.C.s * (X - g.C.r) - g.C.t)) + ε * (0 + 2 * g.C.s) * (ε ^ 2 * (X - g.C.r)) +
      ε ^ 3 * (0 + g.C.r * 0 + 2 * g.C.t) = ε ^ 3 * D := by ring
  rw [hden]
  refine ⟨mul_ne_zero (pow_ne_zero _ ε0) lD0, ?_⟩
  field_simp
  ring

end GlobalTheory.ModelDouble
