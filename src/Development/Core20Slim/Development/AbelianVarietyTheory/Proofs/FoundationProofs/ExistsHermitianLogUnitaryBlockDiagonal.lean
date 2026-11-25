module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

noncomputable section
namespace GlobalTheory.CartanInt.UnitLog
open Formalism.BasicNotions Formalism.BasicNotions.TH    GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator


theorem exists_log {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n ℂ)
    (hu : u ∈ unitary (Matrix n n ℂ)) :
    ∃ H : Matrix n n ℂ, Hᴴ = H ∧ ‖H‖ ≤ Real.pi ∧ u = NormedSpace.exp (Complex.I • H) ∧
      ∀ J, Commute u J → Commute (star u) J → Commute H J := by
  have hn : IsStarNormal u := isStarNormal_of_mem_unitary hu
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  refine ⟨cfc (fun z : ℂ => (Complex.arg z : ℂ)) u, ?_, ?_, ?_, fun J h1 h2 => h1.cfc h2 _⟩
  · rw [← Matrix.star_eq_conjTranspose, ← cfc_star]
    refine cfc_congr fun z _ => ?_
    simp
  · refine norm_cfc_le Real.pi_pos.le fun z _ => ?_
    simpa using Complex.abs_arg_le_pi z
  · rw [← cfc_const_mul Complex.I _ u (hf := hfin.continuousOn _),
      ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp' Complex.exp _ u (hf := hfin.continuousOn _)]
    conv_lhs => rw [← cfc_id' ℂ u]
    refine cfc_congr fun z hz => ?_
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hsph z hz, mul_comm _ Complex.I] at this
    simpa using this.symm

theorem isKC_iff_commute {p q : ℕ} (X : Mat p q) : IsKC X ↔ Commute X (Formalism.UG.Jpq p q) := by
  constructor
  · intro h
    ext a b
    have h1 := h a b
    rcases a with i | i <;> rcases b with j | j <;>
      simp_all [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · intro h a b hab
    have h1 := congrFun (congrFun h.eq a) b
    rcases a with i | i <;> rcases b with j | j <;>
      simp [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at h1 hab ⊢
    · linear_combination (-1 / 2 : ℂ) * h1
    · linear_combination (1 / 2 : ℂ) * h1


end GlobalTheory.CartanInt.UnitLog
