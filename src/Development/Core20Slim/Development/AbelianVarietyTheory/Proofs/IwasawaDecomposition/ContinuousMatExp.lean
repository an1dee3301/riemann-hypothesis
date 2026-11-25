module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.PartialHomeomorph.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.UpqExpChart

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_matExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem exists_chart : ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
    (e : Matrix n n ℂ → Matrix n n ℂ) = NormedSpace.exp ∧ (0 : Matrix n n ℂ) ∈ e.source := by
  open scoped Matrix.Norms.Operator in
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ) :
        Matrix n n ℂ →L[ℂ] Matrix n n ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
  open scoped Matrix.Norms.Operator in
  exact ⟨h.toOpenPartialHomeomorph _, rfl, h.mem_toOpenPartialHomeomorph_source⟩

theorem exp_mul_exp_neg (X : Matrix n n ℂ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Matrix n n ℂ) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

theorem exp_conj_invol {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    NormedSpace.exp (J * X * J) = J * NormedSpace.exp X * J :=
  Matrix.exp_units_conj (⟨J, J, hJ, hJ⟩ : (Matrix n n ℂ)ˣ) X

theorem exp_unitary {J : Matrix n n ℂ} (hJ : J * J = 1) {X : Matrix n n ℂ}
    (hX : Xᴴ * J + J * X = 0) : (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J := by
  have h1 : Xᴴ = J * (-X) * J := by
    have : Xᴴ * J = J * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← this, Matrix.mul_assoc, hJ, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, exp_conj_invol hJ, Matrix.mul_assoc _ J J, hJ,
    Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

theorem exp_twist {J : Matrix n n ℂ} (hJ : J * J = 1) {Z : Matrix n n ℂ}
    (hZ : (NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z = J) :
    NormedSpace.exp (J * (-Z)ᴴ * J) = NormedSpace.exp Z := by
  rw [exp_conj_invol hJ, Matrix.exp_conjTranspose]
  have h1 : (NormedSpace.exp (-Z))ᴴ * (NormedSpace.exp Z)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, exp_mul_exp_neg, Matrix.conjTranspose_one]
  have h2 : (NormedSpace.exp (-Z))ᴴ * J = J * NormedSpace.exp Z := by
    calc (NormedSpace.exp (-Z))ᴴ * J
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z) := by rw [hZ]
      _ = J * NormedSpace.exp Z := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end General




end GlobalTheory.UpqExpChart
