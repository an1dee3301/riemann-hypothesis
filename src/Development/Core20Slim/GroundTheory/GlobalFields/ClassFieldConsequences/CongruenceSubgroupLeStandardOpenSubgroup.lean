module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.Conductor
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ConductorIdeal
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.LocalConductor
public import Init.Classical
public import Init.Core
public import Init.Data.Subtype.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

@[expose] public section

open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

structure Modulus where

  ideal : Ideal (𝓞 K)
  ideal_ne_bot : ideal ≠ ⊥

  real : Set {w : InfinitePlace K // w.IsReal}

variable {K}

namespace IdeleGroup

def positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
    ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)}
  one_mem' w _ := by simp
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul, Units.val_mul, map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.2 (ha w hw)

theorem mem_positiveAt {S : Set {w : InfinitePlace K // w.IsReal}} {x : IdeleGroup K} :
    x ∈ positiveAt S ↔ ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) :=
  Iff.rfl


end IdeleGroup

open IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def exponent (v : HeightOneSpectrum (𝓞 K)) : ℕ := by
  classical
  exact if FiniteMultiplicity v.asIdeal 𝔪.ideal then multiplicity v.asIdeal 𝔪.ideal else 1





theorem finite_support_exponent : (support 𝔪.exponent).Finite := by
  have he (v : HeightOneSpectrum (𝓞 K)) : 𝔪.exponent v = multiplicity v.asIdeal 𝔪.ideal := by
    simp [exponent, FiniteMultiplicity.of_prime_left v.prime 𝔪.ideal_ne_bot]
  simp_rw [funext he]
  have hm : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      v.asIdeal ^ multiplicity v.asIdeal 𝔪.ideal := by
    simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity 𝔪.ideal_ne_bot] using
      Ideal.hasFiniteMulSupport 𝔪.ideal_ne_bot
  rw [← mulSupport_asIdeal_pow]
  exact hm

def congruenceSubgroup : Subgroup (IdeleGroup K) :=
  (idealLevel 𝔪.ideal).comap (toFinite K) ⊓ positiveAt 𝔪.real

theorem mem_congruenceSubgroup {x : IdeleGroup K} :
    x ∈ 𝔪.congruenceSubgroup ↔
      (∀ v, finiteProj v x ∈ unitsLevel v (𝔪.exponent v)) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by
  rw [congruenceSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, idealLevel, mem_finiteLevel,
    mem_positiveAt]
  simp only [finiteComponent_toFinite]
  simp [exponent, FiniteMultiplicity.of_prime_left _ 𝔪.ideal_ne_bot, HeightOneSpectrum.prime]









end Modulus

end

end GroundTheory.Global
