module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Prelude
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_schwartzBruhatProduct_eq_top : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y], Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  first | exact @GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | exact GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | (intros; apply GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top <;> assumption)
