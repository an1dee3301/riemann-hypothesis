module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.Interface
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped WithZero

namespace GroundTheory.Global

section Map

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

def adicCompletionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

theorem continuous_adicCompletionMap : Continuous (adicCompletionMap v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

theorem adicCompletionMap_algebraMap (x : K) :
    adicCompletionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom _
    (uniformContinuous_algebraMap_liesOver K L v w).continuous
    ((algebraMap K (WithVal (v.valuation K)) x : WithVal (v.valuation K)) :
      UniformSpace.Completion (WithVal (v.valuation K))) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

end Map

namespace AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

scoped instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionMap v w).toAlgebra

theorem algebraMap_eq : algebraMap (v.adicCompletion K) (w.adicCompletion L) =
    adicCompletionMap v w :=
  rfl

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_eq, adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L]

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) :=
  continuousSMul_of_algebraMap _ _ (continuous_adicCompletionMap v w)

end AdicLiesOver

section Extension

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem valued_algebraMap_adicCompletion' [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he]
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy : Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) ≠ 0 := by
    simpa using hx
  have h1 := Valued.locally_const hx'
  have h2 := (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).continuousAt.preimage_mem_nhds
    (Valued.locally_const hy)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2
  rw [← hk1, ← hk2, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' v]
  simpa only [Algebra.algebraMap_self, RingHom.id_apply,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot] using
    (valuation_liesOver L v w k).symm

theorem valued_algebraMap_adicCompletion [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [valued_algebraMap_adicCompletion',
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]

instance valuativeExtension_adicCompletion [w.asIdeal.LiesOver v.asIdeal] :
    ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) where
  vle_iff_vle {a b} := by
    have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
    rw [Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)),
      valued_algebraMap_adicCompletion', valued_algebraMap_adicCompletion']
    exact pow_le_pow_iff_left₀ zero_le zero_le he

theorem finite_adicCompletion : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  inferInstance

end Extension

section Check

open AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

end Check

end GroundTheory.Global
