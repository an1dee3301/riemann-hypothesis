module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.ClassFieldConsequences.CongruenceSubgroupLeStandardOpenSubgroup
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.Conductor
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ConductorIdeal
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.LocalConductor
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

theorem Subgroup.subset_of_isPreconnected {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {s : Set G}
    (hs : IsPreconnected s) (h1 : (1 : G) ∈ s) : s ⊆ H :=
  hs.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩ ⟨1, h1, H.one_mem⟩

theorem Subgroup.mem_of_isOpen_of_pos (H : Subgroup ℝˣ) (hH : IsOpen (H : Set ℝˣ)) {r : ℝˣ}
    (hr : 0 < (r : ℝ)) : r ∈ H := by
  let f : ℝ → ℝˣ := fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)
  have hf : Continuous f := Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp
  have hsub := Subgroup.subset_of_isPreconnected H hH (isPreconnected_range hf)
    ⟨0, Units.ext (by simp [f])⟩
  exact hsub ⟨Real.log r, Units.ext (Real.exp_log hr)⟩

theorem Subgroup.mem_of_isOpen_complexUnits (H : Subgroup ℂˣ) (hH : IsOpen (H : Set ℂˣ)) (z : ℂˣ) :
    z ∈ H :=
  Subgroup.subset_of_isPreconnected H hH isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ z)

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem infiniteEmbedding_mem_of_isOpen_of_isReal (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsReal)
    {a : (w.Completion)ˣ}
    (ha : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a : w.Completion)) :
    infiniteEmbedding w a ∈ H := by
  let Hr : Subgroup ℝˣ := (H.comap (infiniteEmbedding w)).comap (realUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hr : Set ℝˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (realUnitsHom hw).continuous
  let r : ℝˣ := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw :
    w.Completion →+* ℝ).toMonoidHom a
  have hr : 0 < (r : ℝ) := by
    change 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (a : w.Completion)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ha
  have hmem : r ∈ Hr := Subgroup.mem_of_isOpen_of_pos Hr hopen hr
  rw [← realUnitsHom_surjective hw a]
  exact hmem

theorem infiniteEmbedding_mem_of_isOpen_of_isComplex (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsComplex)
    (a : (w.Completion)ˣ) : infiniteEmbedding w a ∈ H := by
  let Hc : Subgroup ℂˣ := (H.comap (infiniteEmbedding w)).comap (complexUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hc : Set ℂˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (complexUnitsHom hw).continuous
  have hmem := Subgroup.mem_of_isOpen_complexUnits Hc hopen
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw :
      w.Completion →+* ℂ).toMonoidHom a)
  rw [← complexUnitsHom_surjective hw a]
  exact hmem

theorem Modulus.exists_congruenceSubgroup_le (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup ≤ H := by
  classical
  have hWf : (H.comap ofFinite : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ 𝓝 1 :=
    (hH.preimage continuous_ofFinite).mem_nhds (by simp [H.one_mem])
  obtain ⟨S, n, -, hn0, hsub⟩ := exists_finiteLevel_subset hWf
  have hsupp : (support n).Finite :=
    S.finite_toSet.subset fun v hv ↦ by
      by_contra h
      exact hv (hn0 v h)
  let 𝔪 : Modulus K := ⟨∏ᶠ v, v.asIdeal ^ n v, finprod_asIdeal_pow_ne_bot n, Set.univ⟩
  have hle (v : HeightOneSpectrum (𝓞 K)) : n v ≤ 𝔪.exponent v := by
    rw [exponent, ite_eq_left (FiniteMultiplicity.of_prime_left v.prime 𝔪.ideal_ne_bot)]
    exact (finprod_asIdeal_pow_dvd_iff hsupp (finprod_asIdeal_pow_ne_bot n)).mp dvd_rfl v
  refine ⟨𝔪, rfl, fun x hx ↦ ?_⟩
  obtain ⟨hf, hi⟩ := 𝔪.mem_congruenceSubgroup.1 hx
  rw [← ofFinite_mul_ofInfinite x]
  refine H.mul_mem ?_ ?_
  · have : toFinite K x ∈ finiteLevel n := mem_finiteLevel.2 fun v ↦ by
      rw [finiteComponent_toFinite]
      exact unitsLevel_antitone v (hle v) (hf v)
    exact hsub this
  · rw [ofInfinite_eq_prod]
    refine Subgroup.prod_mem H fun w _ ↦ ?_
    rcases w.isReal_or_isComplex with hw | hw
    · exact infiniteEmbedding_mem_of_isOpen_of_isReal H hH hw (hi ⟨w, hw⟩ (Set.mem_univ _))
    · exact infiniteEmbedding_mem_of_isOpen_of_isComplex H hH hw _



end

end GroundTheory.Global
