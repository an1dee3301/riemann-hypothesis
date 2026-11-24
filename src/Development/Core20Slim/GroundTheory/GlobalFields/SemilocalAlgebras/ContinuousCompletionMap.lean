module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField

noncomputable section

namespace SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (L) in
abbrev PlacesOver (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}

instance (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver (L := L) v) : w.1.asIdeal.LiesOver v.asIdeal :=
  w.2


variable (L) in
def placesOverEquiv (v : HeightOneSpectrum (𝓞 K)) :
    PlacesOver (L := L) v ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun P := ⟨⟨P.1, P.2.1, (have := P.2.2; Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.1)⟩, P.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (v : HeightOneSpectrum (𝓞 K)) : Fintype (PlacesOver (L := L) v) :=
  Fintype.ofEquiv _ (placesOverEquiv (L := L) v).symm

section Map

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom

theorem continuous_completionMap : Continuous (completionMap v w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)

theorem completionMap_algebraMap (x : K) :
    completionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion L) x := by
  apply HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map _
      ((algebraMap K (WithVal (v.valuation K)) x : WithVal _) :
        UniformSpace.Completion (WithVal (v.valuation K))) =
    ((algebraMap K (WithVal (w.valuation L)) x : WithVal _) :
        UniformSpace.Completion (WithVal (w.valuation L)))
  rw [UniformSpace.Completion.map_coe
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w)]
  rfl

theorem valued_completionMap (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 K) w.asIdeal).ne'
  have hK : ∀ k : K, Valued.v (completionMap v w (algebraMap K _ k)) =
      Valued.v (algebraMap K (v.adicCompletion K) k) ^ e := by
    intro k
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion]
    simpa only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self, RingHom.id_apply, he] using
      (HeightOneSpectrum.valuation_liesOver L v w k).symm
  have hclosed : IsClosed
      {x : v.adicCompletion K | Valued.v (completionMap v w x) = Valued.v x ^ e} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x0 hx0
    have h0 : x0 ≠ 0 := by
      rintro rfl
      simp [zero_pow he0] at hx0
    have h1 : Valued.v x0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (completionMap v w x0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (completionMap v w).injective).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_completionMap v w).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with x hx hx'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hx hx' hx0 ⊢
    rwa [hx, hx']
  exact (HeightOneSpectrum.denseRange_algebraMap K v).induction_on x hclosed hK

scoped instance algebraCompletion : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap v w).toAlgebra

theorem algebraMap_completion_eq :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = completionMap v w := rfl

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ (completionMap_algebraMap v w x).symm

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := ((continuous_completionMap v w).comp continuous_fst).mul continuous_snd

end Map

end SemiLocal

end

end GroundTheory.Global
