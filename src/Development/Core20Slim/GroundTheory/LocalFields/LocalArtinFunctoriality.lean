module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinBaseChange
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinTransport
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.LocalFields.FiniteExtension
public import GroundTheory.LocalFields.IntermediateField
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinMap
public import Development.Core20Slim.GroundTheory.LocalFields.MaximalAbelianExtension
public import GroundTheory.LocalFields.SeparableClosure
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem vle_algEquiv_apply_iff {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K L'] [ValuativeRel L] [ValuativeRel L']
    [ValuativeExtension K L] [ValuativeExtension K L'] (e : L ≃ₐ[K] L') (x y : L) :
    e x ≤ᵥ e y ↔ x ≤ᵥ y := by
  rw [vle_iff_spectralNorm_le (K := K), vle_iff_spectralNorm_le (K := K)]
  simp only [spectralNorm, minpoly.algEquiv_eq]

end Valuation

section Conjugation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] (σ : Ω ≃ₐ[K] Ω)

end Conjugation

section Finite

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [IsSepClosure K Ω] [IsSepClosure K' Ω]


omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeExtension K K'] in
theorem maximalAbelianExtension_le_of_algebra {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    y ∈ maximalAbelianExtension K' Ω := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  exact (mem_maximalAbelianExtension_transport_iff (AlgHom.equivFieldRange ι).toRingEquiv
    (RingEquiv.refl Ω) (fun _ => rfl)).1 (maximalAbelianExtension_le_restrictScalars ι.fieldRange hy)

theorem localArtinMap_apply_of_algebra (x : K'ˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
      maximalAbelianExtension K' Ω) : Ω) =
      ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  set e := AlgHom.equivFieldRange ι
  have he : ∀ a b : K', e a ≤ᵥ e b ↔ a ≤ᵥ b := vle_algEquiv_apply_iff e
  have h1 := transport_localArtinMap_apply e.toRingEquiv he (RingEquiv.refl Ω) (fun _ => rfl) x
    (maximalAbelianExtension_le_of_algebra hy)
  simp only [RingEquiv.refl_apply] at h1
  rw [h1, localArtinMap_apply_of_mem ι.fieldRange _ hy]
  congr 3
  ext
  rw [coe_normUnits, coe_normUnits]
  exact Algebra.norm_eq_of_algEquiv e x

end Finite

end GroundTheory.LocalField
