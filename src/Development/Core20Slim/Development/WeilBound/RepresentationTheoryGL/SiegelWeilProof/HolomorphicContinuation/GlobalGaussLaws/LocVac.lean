module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacD
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open Vac

theorem lIvac : LIvac := by
  intro m n ε c t p q e hc hpq S C hS h1 hy hcell
  have hα : ((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)) ≠ 0 := by
    apply mul_ne_zero <;> apply zpow_ne_zero <;> apply pow_ne_zero <;> simp
  have key : ∀ g : GR n, (toBlocks₂₁ (mR g)).det ≠ 0 →
      S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g hg
    obtain ⟨y, h, b, hy0, hb, hh, rfl⟩ := bigcell g hg
    rw [hy y h hy0, hcell h b hb hh, secN_eval ε c t p q hc hpq b hb, vacuum_section_mul_parabolic p q e y h hy0,
      vacuum_section_big_cell p q e h b hh, mul_zpow, mul_zpow]
    field_simp
  have hall : ∀ g, S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g
    exact congrFun (Continuous.ext_on dense_cell hS (continuous_const.mul (continuous_vacuum_section p q e)) key) g
  have hlam := hall 1
  rw [h1, weight_factor_one, mul_one] at hlam
  intro g
  rw [hall g, ← hlam, one_mul]

end PositivityTheory.Rg.Sw.Glob
