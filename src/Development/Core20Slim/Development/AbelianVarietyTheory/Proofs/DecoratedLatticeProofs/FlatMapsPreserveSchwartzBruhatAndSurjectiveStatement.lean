module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
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
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → (p ≤ c + 1 → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix n (n' ⊕ Unit) k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ = Ψ) ∧ (p ≤ c → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix (n ⊕ Unit) n' k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ = Ψ) := by
  first | exact @GlobalTheory.LocFlat.flat_SB_onto | exact GlobalTheory.LocFlat.flat_SB_onto | (intros; apply GlobalTheory.LocFlat.flat_SB_onto <;> assumption)
