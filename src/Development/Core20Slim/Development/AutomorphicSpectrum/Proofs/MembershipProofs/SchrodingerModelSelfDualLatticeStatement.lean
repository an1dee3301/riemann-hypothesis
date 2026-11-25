module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.SchrodingerModelSelfDualLattice
public import Development.Core20Slim.Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_in_schrodinger_span : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  first | exact @GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | exact GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | (intros; apply GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span <;> assumption)
