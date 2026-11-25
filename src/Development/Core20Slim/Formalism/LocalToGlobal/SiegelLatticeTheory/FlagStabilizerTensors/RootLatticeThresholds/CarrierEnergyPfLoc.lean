module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Single
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPfLoc

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gram

variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem inner_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c d : α →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ f c, Finsupp.linearCombination ℂ f d⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ g c, Finsupp.linearCombination ℂ g d⟫_ℂ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

theorem norm_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c : α →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ f c‖ = ‖Finsupp.linearCombination ℂ g c‖ := by
  have hsq : ‖Finsupp.linearCombination ℂ f c‖ ^ 2 = ‖Finsupp.linearCombination ℂ g c‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_lc f g h c c]
  have := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem exists_linearIsometryEquiv_of_inner_eq (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ a, U (f a) = g a := by
  classical
  set F := Finsupp.linearCombination ℂ f with hF
  set G := Finsupp.linearCombination ℂ g with hG
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have := norm_lc f g h c
    rw [← hF, ← hG, hc, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  let φ : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ c, φ ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hφn : ∀ x, ‖φ x‖ = ‖x‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hφ c]
    show ‖G c‖ = ‖F c‖
    exact (norm_lc f g h c).symm
  let L : LinearMap.range F →ₗᵢ[ℂ] V := { φ with norm_map' := hφn }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun a => ?_⟩
  have hfa : f a ∈ LinearMap.range F := ⟨Finsupp.single a 1, by simp [hF]⟩
  have e1 : (L.extend.toLinearIsometryEquiv rfl) (f a) = L.extend (f a) := rfl
  rw [e1, show f a = ((⟨f a, hfa⟩ : LinearMap.range F) : V) from rfl, LinearIsometry.extend_apply]
  have e2 : (⟨f a, hfa⟩ : LinearMap.range F) =
      ⟨F (Finsupp.single a 1), LinearMap.mem_range_self F _⟩ := by
    ext; simp [hF]
  rw [e2]
  show φ _ = g a
  rw [hφ]
  simp [hG]

end Gram

section Loc

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)









end Loc



end Formalism.L2.SG.Pf.Carrier.EnergyPfLoc
