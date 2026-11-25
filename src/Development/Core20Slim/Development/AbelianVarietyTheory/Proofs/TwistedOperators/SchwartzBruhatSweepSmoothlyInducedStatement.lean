module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInduced
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  first | exact @GlobalTheory.SBInduced.sb_induced | exact GlobalTheory.SBInduced.sb_induced | (intros; apply GlobalTheory.SBInduced.sb_induced <;> assumption)
