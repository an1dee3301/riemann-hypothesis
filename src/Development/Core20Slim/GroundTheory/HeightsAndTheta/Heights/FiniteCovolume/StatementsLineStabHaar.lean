module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

section LineStab

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    c • vecAt v x₀ w}
  one_mem' w := ⟨1, by simp⟩
  mul_mem' {a b} ha hb w := by
    obtain ⟨c, hc⟩ := ha w
    obtain ⟨d, hd⟩ := hb w
    refine ⟨c * d, ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hd,
      Matrix.mulVec_smul, hc, smul_smul, mul_comm d c]
  inv_mem' {a} ha w := by
    obtain ⟨c, hc⟩ := ha w
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hz : vecAt v x₀ w = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ) *ᵥ (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    by_cases hc0 : c = 0
    · have h0 : vecAt v x₀ w = 0 := by
        rw [hz, hc, hc0, zero_smul, Matrix.mulVec_zero]
      exact ⟨0, by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    · refine ⟨c⁻¹, ?_⟩
      calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
          = c⁻¹ • ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
              (c • vecAt v x₀ w)) := by
            rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • vecAt v x₀ w := by rw [← hc, ← hz]

omit [NumberField E] in
theorem mem_lineStab {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W} {g : archUnitary h v} :
    g ∈ lineStab h v x₀ ↔ ∀ w, ∃ c : ℂ,
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = c • vecAt v x₀ w :=
  Iff.rfl


omit [NumberField E] in
theorem vecFixGroup_le_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    vecFixGroup h v x₀ ≤ lineStab h v x₀ := fun g hg w => ⟨1, by rw [one_smul]; exact hg w⟩


omit [NumberField E] in
theorem isClosed_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (lineStab h v x₀ : Set (archUnitary h v)) := by
  have : (lineStab h v x₀ : Set (archUnitary h v)) = ⋂ w, (fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) ⁻¹'
        (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Submodule.mem_span_singleton,
      mem_lineStab]
    exact forall_congr' fun w => ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  rw [this]
  refine isClosed_iInter fun w => IsClosed.preimage ?_ (Submodule.closed_of_finiteDimensional _)
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const

instance locallyCompactSpace_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (lineStab h v x₀) :=
  (isClosed_lineStab h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

end LineStab

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LineStabHaar.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∀ (μP : Measure (lineStab h v x₀)) [μP.IsHaarMeasure],
    ∃ (ν : Measure (vecFixGroup h v x₀)) (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ Measurable τ ∧ (∀ b, τ b ∈ lineStab h v x₀) ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ φ : archUnitary h v → ℝ≥0∞, Measurable φ →
        ∫⁻ p, φ (p : archUnitary h v) ∂μP = ∫⁻ b : InfinitePlace E → ℂ,
          (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
            ∫⁻ x : vecFixGroup h v x₀, φ ((x : archUnitary h v) * τ b) ∂ν

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
