module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjoint
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementP
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJ
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLog
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoords
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatrices
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobian
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversal
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU  Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.CartanInt

variable {p q : ℕ}

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]





end GlobalTheory.CartanInt
