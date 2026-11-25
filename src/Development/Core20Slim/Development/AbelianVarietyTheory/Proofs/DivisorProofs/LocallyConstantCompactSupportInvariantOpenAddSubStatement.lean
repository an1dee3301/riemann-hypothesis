module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantCompactSupportInvariantOpenAddSub
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g → ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  first | exact @GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | exact GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | (intros; apply GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup <;> assumption)
