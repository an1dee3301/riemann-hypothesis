module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise





theorem latI_eq_smul {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K))
    (δ : ℂ) : latI φ 𝔞 δ = δ • latI φ 𝔞 1 := by
  unfold latI
  rw [AddSubgroup.pointwise_smul_def]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    exact AddSubgroup.mem_map.2 ⟨φ c, AddSubgroup.subset_closure ⟨c, hc, (one_mul _).symm⟩, rfl⟩
  · refine AddSubgroup.map_le_iff_le_comap.2 ?_
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨c, hc, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, hc, show δ * (1 * φ c) = δ * φ c by rw [one_mul]⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
