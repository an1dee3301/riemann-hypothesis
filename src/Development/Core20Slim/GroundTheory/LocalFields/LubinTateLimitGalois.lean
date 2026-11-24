module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.LubinTateTowerMaps
public import Development.Core20Slim.GroundTheory.LocalFields.ExamplesLaurent
public import GroundTheory.LocalFields.UnitsBasic
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

open IntermediateField Topology Filter

namespace GroundTheory.LocalField

open ValuativeRel

section Finite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]


end Finite

section UnitsTopology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]


theorem FormalGroup.unitsMk_eq_one_iff {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {u : 𝒪[K]ˣ} :
    FormalGroup.unitsMk π n u = 1 ↔ u ∈ unitFiltration K n := by
  rw [mem_unitFiltration, ← Units.val_eq_one, FormalGroup.coe_unitsMk, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]



end UnitsTopology

namespace FormalGroup


section Limit

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}


variable (Ω) in
def lubinTateLimit (hπ : Irreducible π) : IntermediateField K Ω :=
  ⨆ n, lubinTateField Ω hπ (isLubinTateSeries_ltPoly π) n


variable [IsSepClosed Ω]




instance isGalois_lubinTateLimit : IsGalois K (lubinTateLimit Ω hπ) := by
  unfold lubinTateLimit
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩















end Limit

end FormalGroup

end GroundTheory.LocalField
