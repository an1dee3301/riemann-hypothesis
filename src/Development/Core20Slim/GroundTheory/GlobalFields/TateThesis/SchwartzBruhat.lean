module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TracePairing
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure Filter
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap FourierTransform Real Classical

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem infiniteTrace_mul (x y : InfiniteAdeleRing K) :
    infiniteTrace K (x * y) =
      mixedTraceForm K (homeomorphMixedSpace K x) (homeomorphMixedSpace K y) := by
  rw [← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_mul, mixedTraceForm_apply]

theorem adelicChar_mul_eq (x y : 𝔸[K]) :
    (adelicChar K (x * y) : ℂ) =
      (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K x.1) (homeomorphMixedSpace K y.1)) : ℂ) *
        (finiteAdelicChar K (x.2 * y.2) : ℂ) := by
  have hxy : x * y = infiniteAdeleInl (x.1 * y.1) + finiteAdeleInr (x.2 * y.2) :=
    (infiniteAdeleInl_add_finiteAdeleInr (x * y)).symm
  have hinf : adelicChar K (infiniteAdeleInl (x.1 * y.1)) = 𝐞 (-infiniteTrace K (x.1 * y.1)) :=
    adelicChar_infinite _
  rw [hxy, AddChar.map_add_eq_mul, Circle.coe_mul, hinf, infiniteTrace_mul, finiteAdelicChar_apply]

def schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ)) (g : 𝔸ᶠ[K] → ℂ) : 𝔸[K] → ℂ :=
  fun x ↦ φ (homeomorphMixedSpace K x.1) * g x.2


variable (K) in
def schwartzBruhat : Submodule ℂ (𝔸[K] → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : 𝓢(mixedSpace K, ℂ), ∃ g ∈ finiteSchwartzBruhat K,
    F = schwartzBruhatTensor φ g}

theorem schwartzBruhatTensor_mem (φ : 𝓢(mixedSpace K, ℂ)) {g : 𝔸ᶠ[K] → ℂ}
    (hg : g ∈ finiteSchwartzBruhat K) : schwartzBruhatTensor φ g ∈ schwartzBruhat K :=
  Submodule.subset_span ⟨φ, g, hg, rfl⟩


















end

end GroundTheory.Global
