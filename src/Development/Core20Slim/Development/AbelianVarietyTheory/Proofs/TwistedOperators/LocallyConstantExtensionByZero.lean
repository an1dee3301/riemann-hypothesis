module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

noncomputable section
namespace GlobalTheory.SBExtend

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]

end GlobalTheory.SBExtend
