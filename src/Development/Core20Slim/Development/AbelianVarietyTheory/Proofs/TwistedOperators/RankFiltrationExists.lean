module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


omit [DecidableEq a] [DecidableEq b] in
theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ



end

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
