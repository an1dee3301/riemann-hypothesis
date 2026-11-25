module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem CoeffLatticeBasis.proof (E : Type*) [Field E] [NumberField E] :
    CoeffLatticeBasis.Statement E := by
  intro A hO hfg
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).mpr hfg
  obtain ⟨n, b⟩ : Σ n : ℕ, Basis (Fin n) ℤ A := Module.basisOfFiniteTypeTorsionFree'

  let f : A →ₗ[ℤ] E := A.subtype.toIntLinearMap
  let v : Fin n → E := fun i => (b i : E)
  have hv : v = f ∘ b := rfl
  have hliZ : LinearIndependent ℤ v :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ

  have hA : ∀ a ∈ A, a ∈ Submodule.span ℚ (Set.range v) := by
    intro a ha
    have h1 : f ⟨a, ha⟩ ∈ Submodule.span ℤ (f '' Set.range b) :=
      Submodule.apply_mem_span_image_of_mem_span f (b.mem_span _)
    rw [← Set.range_comp, ← hv] at h1
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h1
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← (integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact hA _ (hO ⟨_, rfl⟩)
  have hn : finrank ℚ E = n := by
    rw [finrank_eq_card_basis (Basis.mk hliQ hsp), Fintype.card_fin]
  exact ⟨b.reindex (finCongr hn.symm)⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
