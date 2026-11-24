module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (K) in
def below (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.under (𝓞 K)
  isPrime := Ideal.IsPrime.under (𝓞 K) w.asIdeal
  ne_bot := Ideal.under_ne_bot (𝓞 K) w.ne_bot

instance liesOver_below (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (below K w).asIdeal :=
  ⟨rfl⟩


omit [NumberField K] [NumberField L] in
theorem below_eq_iff (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) :
    below K w = v ↔ w.asIdeal.LiesOver v.asIdeal := by
  constructor
  · rintro rfl
    infer_instance
  · intro h
    exact HeightOneSpectrum.ext h.over.symm

theorem tendsto_below : Tendsto (below K (L := L)) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦
    ((Set.finite_range (Subtype.val : PlacesOver (L := L) v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ⟨⟨w, (below_eq_iff w v).1 hw⟩, rfl⟩).to_subtype

theorem completionMap_congr {v v' : HeightOneSpectrum (𝓞 K)} (h : v = v')
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v'.asIdeal]
    (a : FiniteAdeleRing (𝓞 K) K) :
    completionMap v w (a v) = completionMap v' w (a v') := by
  subst h
  rfl

theorem mapsTo_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Set.MapsTo (completionMap v w) (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [valued_completionMap]
  exact pow_le_one' hx _


variable (K L) in
def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (B₁ := fun v ↦ v.adicCompletionIntegers K) (B₂ := fun w ↦ w.adicCompletionIntegers L)
    (below K) tendsto_below (fun w ↦ completionMap (below K w) w)
    (hφ := .of_forall fun w ↦ mapsTo_completionMap (below K w) w)

@[simp]
theorem finiteAdeleMap_apply (x : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleMap K L x w = completionMap (below K w) w (x (below K w)) :=
  rfl

theorem continuous_finiteAdeleMap : Continuous (finiteAdeleMap K L) :=
  RestrictedProduct.mapAlong_continuous _ _ (below K) tendsto_below _
    (.of_forall fun w ↦ mapsTo_completionMap (below K w) w) fun w ↦ continuous_completionMap (below K w) w

theorem finiteAdeleMap_algebraMap (k : K) :
    finiteAdeleMap K L (algebraMap K _ k) = algebraMap L _ (algebraMap K L k) := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  exact (completionMap_algebraMap (below K w) w k).trans
    (IsScalarTower.algebraMap_apply K L (w.adicCompletion L) k)

end AdeleBaseChange

end

end GroundTheory.Global
