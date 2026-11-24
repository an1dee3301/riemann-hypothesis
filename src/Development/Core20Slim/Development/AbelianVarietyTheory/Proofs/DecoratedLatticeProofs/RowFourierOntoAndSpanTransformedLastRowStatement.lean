module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_fourier_onto_and_span_transformed_last_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z], (∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) ∧ ∀ Ξ₂ : SB (Matrix (Z ⊕ Unit) n k), ∃ (N : ℕ) (a : Fin N → SB (Matrix Z n k)) (c : Fin N → SB (Matrix n Unit k)) (g : Fin N → SB (Matrix (Z ⊕ Unit) n k)), (∀ i x, (g i).1 x = (a i).1 x.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => (c i).1 (Matrix.of fun r _ => y r)) (x (Sum.inr ()))) ∧ Ξ₂ = ∑ i, g i := by
  first | exact @GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | exact GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow | (intros; apply GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow <;> assumption)
