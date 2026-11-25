module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelePoisson
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TraceDualLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TracePairing
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Automorphic.Adele2

open GroundTheory.Global NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure Filter
  Matrix
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap FourierTransform Real Classical
  nonZeroDivisors

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]



























theorem finiteFourier_cosetIndicator_algebraMap {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : 𝔸ᶠ[K]}
    {c : K} (hc : b - algebraMap K 𝔸ᶠ[K] c ∈ idealFiniteAdeles I) (η : K) :
    finiteFourier K (cosetIndicator I b) (algebraMap K 𝔸ᶠ[K] η) =
      ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) *
        if η ∈ (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) then
          (𝐞 (mixedTraceForm K (mixedEmbedding K η) (mixedEmbedding K c)) : ℂ) else 0 := by
  rw [finiteFourier_cosetIndicator]
  by_cases hη : η ∈ (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)
  · have hη' : algebraMap K 𝔸ᶠ[K] η ∈ idealFiniteAdeles (traceDualIdeal K I) :=
      (algebraMap_mem_idealFiniteAdeles_iff _ η).mpr hη
    rw [if_pos hη, Set.indicator_of_mem (SetLike.mem_coe.mpr hη'), Pi.one_apply, mul_one]
    have hb : b * algebraMap K 𝔸ᶠ[K] η = algebraMap K 𝔸ᶠ[K] c * algebraMap K 𝔸ᶠ[K] η +
        (b - algebraMap K 𝔸ᶠ[K] c) * algebraMap K 𝔸ᶠ[K] η := by ring
    rw [hb, AddChar.map_add_eq_mul, (forall_finiteAdelicChar_mul_eq_one_iff I _).mpr hη' _ hc,
      mul_one, finiteAdelicChar_algebraMap_mul, mixedTraceForm_comm K (mixedEmbedding K c)]
  · have hη' : algebraMap K 𝔸ᶠ[K] η ∉ idealFiniteAdeles (traceDualIdeal K I) :=
      fun h ↦ hη ((algebraMap_mem_idealFiniteAdeles_iff _ η).mp h)
    rw [if_neg hη, Set.indicator_of_notMem (by simpa using hη'), mul_zero, mul_zero]










def infRingHom : 𝔸[K] →+* mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.comp (RingHom.fst _ _)

def finRingHom : 𝔸[K] →+* 𝔸ᶠ[K] := RingHom.snd _ _














end

end GroundTheory.Automorphic.Adele2
