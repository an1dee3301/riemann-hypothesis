module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsStd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_model_selfDual_lattice : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R))), GoodChar ψ O u → IsModel ψ d μ S → ∃ (Γ : AddSubgroup W) (al : W → ℂ) (φ : SB (κ → R)), SelfDual S Γ ∧ IsSemi S al Γ ∧ Law S al Γ φ ∧ Cyclic S φ ∧ φ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.StdLattice.exists_std | exact GlobalTheory.CompanionTheory.StdLattice.exists_std | (intros; apply GlobalTheory.CompanionTheory.StdLattice.exists_std <;> assumption)
