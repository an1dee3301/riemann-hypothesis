module

public import Mathlib
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PI

def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}

def area (Λ : AddSubgroup ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, a = |((starRingEnd ℂ) w₁ * w₂).im|}

def U1 (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + ω) * Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2

def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3

def discr (Λ : AddSubgroup ℂ) : ℂ := g2 Λ ^ 3 - 27 * g3 Λ ^ 2

end PI

end
