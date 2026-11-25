module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

attribute [local instance high] FaithfulSMul.to_isTorsionFree

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]





end DVR

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

instance isSeparable_fractionRing_integer [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  have H : RingHom.comp (algebraMap (FractionRing 𝒪[K]) (FractionRing 𝒪[L]))
      ↑(FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors 𝒪[K])
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H


variable [FiniteDimensional K L]

section Separable

variable [Algebra.IsSeparable K L]



end Separable

variable {K L}


section Separable

variable [Algebra.IsSeparable K L]




variable (K L)

end Separable

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional K L] [FiniteDimensional L M] [Algebra.IsSeparable K M]



end Tower

section Discriminant


variable [Algebra.IsSeparable K L]

variable (K L)

end Discriminant

end GroundTheory.LocalField
