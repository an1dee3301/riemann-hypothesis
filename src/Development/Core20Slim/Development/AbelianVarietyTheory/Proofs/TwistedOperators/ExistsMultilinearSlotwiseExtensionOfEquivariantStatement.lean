module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariant
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap (RingHom.id ℂ) H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap (RingHom.id ℂ) H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  first | exact @GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | exact GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | (intros; apply GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension <;> assumption)
