module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.TowerDrop

theorem archimedeanRallisFourth_of_discreteSeriesBlattner : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  intro X _ _ hD h5
  refine ⟨fun t al be ga de hd i hi hr hs MM f hf => ?_,
    fun t al be ga de hd i hi hr hs MM f hf => ?_⟩
  · exact ((GlobalTheory.LowerTower.no_map_lower X hD h5 t al be ga de hd.1 i hi).1 hr hs) MM f hf
  · have hA := hd.1
    have ht : 1 ≤ t := hA.1
    have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
    have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
    obtain ⟨-, hpar, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    obtain ⟨-, -, hsign, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := (GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi).2.1 hr hs
    refine GlobalTheory.LowerTower.tensNo_first X hD h5 (by omega) _ hpar 0 ?_ hno MM f hf
    rw [GlobalTheory.SmallerSource.cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (GlobalTheory.LowerTower.lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith

end GlobalTheory.TowerDrop
