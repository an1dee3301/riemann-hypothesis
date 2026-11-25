module

public import Mathlib
public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.UnitsBasic
public import GroundTheory.LocalFields.Interface
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def integerAlgEquivLocal (σ : L ≃ₐ[K] L) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L] :=
  AlgEquiv.ofAlgHom (integerAlgHom σ.toAlgHom) (integerAlgHom σ.symm.toAlgHom)
    (AlgHom.ext fun x => Subtype.ext (σ.apply_symm_apply (x : L)))
    (AlgHom.ext fun x => Subtype.ext (σ.symm_apply_apply (x : L)))

instance integerUnitsAction : MulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ where
  smul σ u := Units.map (integerAlgEquivLocal σ : 𝒪[L] →* 𝒪[L]) u
  one_smul u := by ext; rfl
  mul_smul σ τ u := by ext; rfl
  smul_mul σ u w := map_mul (Units.map (integerAlgEquivLocal σ : 𝒪[L] →* 𝒪[L])) u w
  smul_one σ := map_one (Units.map (integerAlgEquivLocal σ : 𝒪[L] →* 𝒪[L]))

theorem unitsIncl_smul (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    unitsIncl L (σ • u) = σ • unitsIncl L u := by
  ext
  change ((integerAlgEquivLocal σ) (u : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L)
  rfl

end GroundTheory.LocalField
