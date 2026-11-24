module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.RgEis

def Twist : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (Γ K S P P' : Subgroup G) (c c₀ : G → ℂ) (η η' β ξ : G → ℝ) (N : ℝ), IsCompact (K : Set G) → IsCh Γ ⊤ c₀ →
    IsPar Γ K S c → IsPar Γ K P c → IsPar Γ K P' c →
    ((AllRep K fun ρ => HasWall Γ K P P' c η η' β ρ) → AllRep K fun ρ => HasWall Γ K P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasFirst Γ K S P P' c η η' β ρ) → AllRep K fun ρ => HasFirst Γ K S P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasLast Γ K S P P' c η η' β ξ N ρ) → AllRep K fun ρ => HasLast Γ K S P P' (c * c₀) η η' β ξ N ρ)

def Scale : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β l : G → ℝ) (s : ℝ), 0 < s →
  IsHt Γ K ⊤ l → HasWall Γ K P P' c η η' β ρ →
  HasWall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ

end PositivityTheory.RgEis
