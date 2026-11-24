module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped ContDiff Topology

namespace GlobalTheory

theorem hasFDerivAt_of_continuous_coordinate_line_derivs :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) →
      (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) →
      ∀ t, HasFDerivAt F
        (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by
  intro k F G hG hF t
  refine hasFDerivAt_of_continuous_partials k F G (fun i t => ?_) hG t
  have h0 : HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) (t i - t i) := by
    rw [sub_self]
    exact hF i t
  have h1 := h0.comp_sub_const (t i) (t i)
  have hfun : (fun s : ℝ => F (Function.update t i s)) =
      fun s : ℝ => F (t + (s - t i) • Pi.single i 1) := by
    funext s
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [hfun]
  exact h1

end GlobalTheory
