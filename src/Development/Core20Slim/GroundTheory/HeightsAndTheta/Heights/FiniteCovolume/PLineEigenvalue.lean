module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineStabHaar
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def LineEigenvalue.coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (g : archUnitary h v) (w : InfinitePlace E) : ℂ :=
  ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) (i w)) / vecAt v x₀ w (i w)


omit [NumberField E] in
theorem LineEigenvalue.continuous_coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (w : InfinitePlace E) :
    Continuous fun g : archUnitary h v => coordRatio h v x₀ i g w := by
  unfold coordRatio
  refine Continuous.div_const ?_ _
  exact (continuous_apply (i w)).comp
    ((Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
      continuous_const)


omit [NumberField E] in
theorem LineEigenvalue.mulVec_eq_coordRatio {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) :
    ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      coordRatio h v x₀ i g w • vecAt v x₀ w := by
  obtain ⟨c, hc⟩ := hg w
  have e : coordRatio h v x₀ i g w = c := by
    rw [coordRatio, hc, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (hi w), mul_one]
  rw [e, hc]

theorem LineEigenvalue.coordRatio_ne_zero {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) : coordRatio h v x₀ i g w ≠ 0 := by
  intro h0
  have e := mulVec_eq_coordRatio hi hg w
  rw [h0, zero_smul] at e
  apply hi w
  have hX : vecAt v x₀ w = (((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ
      (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w)) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hX, e, Matrix.mulVec_zero, Pi.zero_apply]

theorem LineEigenvalue.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : VecAtNeZero.Statement v) : LineEigenvalue.Statement h v := by
  intro x₀ hx₀
  have hne : ∀ w, ∃ j, vecAt v x₀ w j ≠ 0 := fun w => by
    simpa using Function.ne_iff.mp (h1 x₀ hx₀ w)
  choose i hi using hne
  refine ⟨fun p w => Units.mk0 (coordRatio h v x₀ i (p : archUnitary h v) w)
    (coordRatio_ne_zero hi p.2 w), ?_, fun p w => ?_⟩
  · refine continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_coordRatio h v x₀ i w).comp continuous_subtype_val
    · simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
      exact ((continuous_coordRatio h v x₀ i w).comp continuous_subtype_val).inv₀
        fun p => coordRatio_ne_zero hi p.2 w
  · rw [Units.val_mk0]
    exact mulVec_eq_coordRatio hi p.2 w


end

end GroundTheory.Heights₂.Heights.FiniteCovolume
