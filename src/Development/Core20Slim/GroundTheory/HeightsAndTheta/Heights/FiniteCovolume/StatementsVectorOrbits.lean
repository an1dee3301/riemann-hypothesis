module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Units

variable (E : Type*) [Field E] [NumberField E]

def congruenceUnits (N : ℕ) : Subgroup (𝓞 E)ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})).toMonoidHom).ker

omit [NumberField E] in
variable {E} in
theorem mem_congruenceUnits {N : ℕ} {ε : (𝓞 E)ˣ} :
    ε ∈ congruenceUnits E N ↔ (ε : 𝓞 E) - 1 ∈ Ideal.span {(N : 𝓞 E)} := by
  rw [congruenceUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk _),
    Ideal.Quotient.eq]

def CongruenceUnitsFiniteIndex.Statement : Prop :=
  ∀ N : ℕ, 0 < N → (congruenceUnits E N).index ≠ 0

end Units

section Groups

def BoundedIndexSubgroupsFinite.Statement (G : Type*) [AddCommGroup G] : Prop :=
  ∀ A B : AddSubgroup G, B.FG → A ≤ B → ∀ C : ℕ,
    {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C}.Finite

end Groups

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsotropicScaling.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ : W), IsLattice E La → IsIntegralOn h La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∃ N : ℕ, 0 < N ∧ ∀ ε ∈ congruenceUnits E N,
      ∃ γ ∈ latticeStab h La, γ • x₀ = ((ε : 𝓞 E) : E) • x₀

end Spaces

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
