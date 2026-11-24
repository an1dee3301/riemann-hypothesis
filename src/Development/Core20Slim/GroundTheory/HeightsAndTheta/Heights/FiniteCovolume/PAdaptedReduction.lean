module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdaptedReduction
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHyperbolicPairs
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLineNormalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementLattice
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

section Transport

variable {h : HermitianForm F E W}

theorem sesq_unitary_smul (g : h.unitaryGroup) (x y : W) :
    h.toSesq (g • x) (g • y) = h.toSesq x y :=
  g.2 x y

theorem unitary_smul_scalar_smul (g : h.unitaryGroup) (a : E) (x : W) : g • (a • x) = a • (g • x) :=
  map_smul (g : W ≃ₗ[E] W) a x

theorem mem_inv_smul_iff {g : h.unitaryGroup} {La : AddSubgroup W} {x : W} :
    x ∈ g⁻¹ • La ↔ g • x ∈ La := by
  change x ∈ ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) • La ↔ _
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem lineCoeffs_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) (x : W) :
    lineCoeffs (E := E) (g⁻¹ • La) x = lineCoeffs (E := E) La (g • x) := by
  ext a
  change a • x ∈ g⁻¹ • La ↔ a • (g • x) ∈ La
  rw [mem_inv_smul_iff, unitary_smul_scalar_smul]

theorem dualLattice_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) :
    dualLattice h (g⁻¹ • La) = g⁻¹ • dualLattice h La := by
  ext y
  rw [mem_inv_smul_iff]
  change (∀ x ∈ g⁻¹ • La, h.toSesq y x ∈ integralClosure ℤ E) ↔
    ∀ x ∈ La, h.toSesq (g • y) x ∈ integralClosure ℤ E
  constructor
  · intro hy x hx
    have hx' : g⁻¹ • x ∈ g⁻¹ • La := by rw [mem_inv_smul_iff, smul_inv_smul]; exact hx
    have := hy _ hx'
    rwa [← sesq_unitary_smul g, smul_inv_smul] at this
  · intro hy x hx
    rw [mem_inv_smul_iff] at hx
    rw [← sesq_unitary_smul g]
    exact hy _ hx

theorem isDIntegral_inv_smul (g : h.unitaryGroup) {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) : IsDIntegral h D (g⁻¹ • La) := by
  set γ : W ≃ₗ[E] W := ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) with hγ
  have hinj : Function.Injective (DistribMulAction.toAddMonoidEnd (W ≃ₗ[E] W) W γ) :=
    fun x y hxy => γ.injective hxy
  have hrel : (g⁻¹ • La).relIndex (dualLattice h (g⁻¹ • La)) =
      La.relIndex (dualLattice h La) := by
    rw [dualLattice_inv_smul]
    change (γ • La).relIndex (γ • dualLattice h La) = _
    rw [AddSubgroup.pointwise_smul_def, AddSubgroup.pointwise_smul_def]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a x hx
    rw [mem_inv_smul_iff] at hx ⊢
    rw [unitary_smul_scalar_smul]
    exact hLa.isLattice.smul_mem a _ hx
  · have hfg := hLa.isLattice.fg
    change (γ • La).FG
    rw [AddSubgroup.pointwise_smul_def]
    rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hfg ⊢
    obtain ⟨k, f, hf⟩ := hfg
    exact ⟨k, γ.toLinearMap.toAddMonoidHom.comp f, by
      rw [AddMonoidHom.range_comp, hf]
      rfl⟩
  · have hset : ((g⁻¹ • La : AddSubgroup W) : Set W) =
        γ.toLinearMap '' (La : Set W) := by
      ext y
      constructor
      · intro hy
        exact ⟨g • y, mem_inv_smul_iff.1 hy, inv_smul_smul g y⟩
      · rintro ⟨x, hx, rfl⟩
        change g⁻¹ • x ∈ g⁻¹ • La
        rw [mem_inv_smul_iff, smul_inv_smul]
        exact hx
    rw [hset, Submodule.span_image, hLa.isLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact LinearEquiv.surjective _
  · intro x hx y hy
    rw [mem_inv_smul_iff] at hx hy
    rw [← sesq_unitary_smul g]
    exact hLa.integral _ hx _ hy
  · rw [hrel]
    exact hLa.index_ne_zero
  · rw [hrel]
    exact hLa.index_le

end Transport

theorem AdaptedReduction.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : HyperbolicPairTransitive.Statement h) (h₂ : LineNormalForm.Statement h)
    (h₃ : ComplementLattice.Statement h) : AdaptedReduction.Statement h := by
  intro v₀ w₀ hp h' hh' D
  obtain ⟨KK, hKK, n, hn, H⟩ := h₂ D
  obtain ⟨D', hD'⟩ := h₃ v₀ w₀ hp h' hh' D n hn
  refine ⟨KK, hKK, n, D', hn, fun La l hLa hl => ?_⟩
  obtain ⟨v, w, hvl, hvw, hK, hdec⟩ := H La l hLa hl
  obtain ⟨g, hgv, hgw⟩ := h₁ v₀ w₀ v w hp hvw
  have hI : lineCoeffs (E := E) (g⁻¹ • La) v₀ = lineCoeffs (E := E) La v := by
    rw [lineCoeffs_inv_smul, hgv]
  have hJ : lineCoeffs (E := E) (g⁻¹ • La) w₀ = lineCoeffs (E := E) La w := by
    rw [lineCoeffs_inv_smul, hgw]
  have hwv : h.toSesq w v = 1 := by
    rw [← h.isSymm.eq v w, hvw.2.2, map_one]
  have hsplit : ∀ x ∈ g⁻¹ • La, ∃ a ∈ lineCoeffs (E := E) (g⁻¹ • La) v₀,
      ∃ b ∈ lineCoeffs (E := E) (g⁻¹ • La) w₀,
        n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀ := by
    intro x hx
    rw [mem_inv_smul_iff] at hx
    obtain ⟨ha, hb⟩ := hdec _ hx
    refine ⟨(n : E) * h.toSesq w (g • x), by rw [hI]; exact ha,
      (n : E) * h.toSesq v (g • x), by rw [hJ]; exact hb, ?_⟩
    rw [mem_hypComplement, ← sesq_unitary_smul g v₀, ← sesq_unitary_smul g w₀, hgv, hgw,
      ← Nat.cast_smul_eq_nsmul E, smul_sub, smul_sub, unitary_smul_scalar_smul, unitary_smul_scalar_smul,
      unitary_smul_scalar_smul, hgv, hgw]
    simp only [map_sub, map_smul, smul_eq_mul, hvw.1, hvw.2.1, hvw.2.2, hwv]
    constructor <;> ring
  refine ⟨g, g⁻¹ • La, smul_inv_smul g La, hgv ▸ hvl, ?_, hsplit,
    hD' _ (isDIntegral_inv_smul g hLa) hsplit⟩
  rw [hI, hJ]
  exact hK

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
