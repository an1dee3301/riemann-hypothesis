module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Group

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ParabolicDecomposition.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : KTransitive.Statement ι) (h₂ : HermAtPlace.Statement h v)
    (h₃ : GramAtData.Statement h v) (h₄ : ArchInvariant.Statement h v)
    (h₅ : VecAtNeZero.Statement v) : ParabolicDecomposition.Statement h v := by
  intro M x₀ hx₀ hiso g
  have hz : ∀ w, vecAt v x₀ w ≠ 0 := h₅ x₀ hx₀
  have hzi : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← h₂, hiso, map_zero]
  have hzi' : ∀ w, star (invApply g (vecAt v x₀) w) ⬝ᵥ
      (gramAt h v w *ᵥ invApply g (vecAt v x₀) w) = 0 := fun w => by
    rw [h₄, hzi]

  have hginv : ∀ w, (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := fun w => rfl
  have hz' : ∀ w, invApply g (vecAt v x₀) w ≠ 0 := by
    intro w hw
    apply hz w
    have e : ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ invApply g (vecAt v x₀) w =
        vecAt v x₀ w := by
      rw [invApply, hginv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← e, hw, Matrix.mulVec_zero]
  have hmaj : ∀ w, IsMajorantOf (gramAt h v w) (M.P w) := fun w =>
    ⟨M.posDef w, (h₃ w).1, (h₃ w).2, M.siegel w⟩
  choose k hkH hkP c hc using fun w =>
    h₁ _ _ (hmaj w) _ _ (hz w) (hz' w) (hzi w) (hzi' w)
  have hkA : k ∈ archUnitary h v := (Subgroup.mem_pi _).2 fun w _ => hkH w
  set kk : archUnitary h v := ⟨k, hkA⟩ with hkk
  have hkS : kk ∈ M.stab := by
    rw [Majorant.stab, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_pi _).2 fun w _ => hkP w
  refine ⟨g * kk⁻¹, kk, hkS, by group, fun w => ⟨(c w)⁻¹, ?_⟩⟩
  have hcw : c w ≠ 0 := by
    intro h0
    apply hz' w
    have e := congrArg (fun y => (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at e
    exact e

  have hk : (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      (c w)⁻¹ • invApply g (vecAt v x₀) w := by
    have e := congrArg (fun y => (c w)⁻¹ • ((((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y)) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hcw, one_smul] at e
    exact e.symm
  have hp : (((g * kk⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) * (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := rfl
  rw [hp, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, invApply, hginv, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
