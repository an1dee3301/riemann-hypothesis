module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.AdeleDual

open GroundTheory.Global

variable {F : Type} [Field F] [NumberField F]

theorem exists_eq_adelicChar_mul (χ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hc : Continuous χ)
    (hF : ∀ a : F, χ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) :
    ∃ ξ : F, ∀ x, χ x = (adelicChar F (algebraMap F (AdeleRing (𝓞 F) F) ξ * x) : ℂ) := by
  have hn := GlobalTheory.CompanionTheory.AdeleAnn.norm_eq_one χ hc hF
  let χ' : AddChar (AdeleRing (𝓞 F) F) Circle :=
    { toFun := fun y => ⟨χ y, mem_sphere_zero_iff_norm.2 (hn y)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (χ.map_add_eq_mul a b) }
  have hχ' : Continuous χ' := hc.subtype_mk _
  obtain ⟨ξ, hξ, -⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul χ' hχ' fun k => Circle.ext (hF k)
  exact ⟨ξ, fun x => congrArg (fun c : Circle => (c : ℂ)) (hξ x)⟩

end GlobalTheory.CompanionTheory.AdeleDual
