module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem IsDerFam.hasDerivAt_exp {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {l : List (Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F l (z * NormedSpace.exp (t • X))) (F (X :: l) (z * NormedSpace.exp (s • X))) s := by
  have h1 := hF l hl X hX _ (mul_mem_UJ hz (exp_mem_UJ hX s))
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = F l (z * _ * _)
  rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem norm_sub_le_of_deriv_Icc {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {δ B : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s ∈ Set.Icc (-δ) δ, ‖f' s‖ ≤ B) {t : ℝ} (ht : t ∈ Set.Icc (-δ) δ) : ‖f t - f 0‖ ≤ B * |t| := by
  have := (convex_Icc (-δ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hB (x := 0) (y := t) ⟨by linarith, hδ⟩ ht
  simpa using this

end GlobalTheory.TypeSum
