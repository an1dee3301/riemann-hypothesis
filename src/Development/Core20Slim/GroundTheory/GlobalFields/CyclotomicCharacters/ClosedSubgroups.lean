module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology
open scoped GroundTheory.LocalField.Abstract

namespace GroundTheory.Global

namespace Cyclotomic

open GroundTheory.LocalField.Abstract

section Padic

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

end Padic

section ProfiniteInteger

def factorialPNat (n : ℕ) : ℕ+ := ⟨(n + 1).factorial, Nat.factorial_pos _⟩

theorem tendsto_natCast (a : ℤ̂) :
    Tendsto (fun n : ℕ => (((ProfiniteInteger.proj (factorialPNat n) a).val : ℕ) : ℤ̂)) atTop
      (𝓝 a) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro m
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop (m : ℕ)] with n hn
  have hdvd : (m : ℕ) ∣ (factorialPNat n : ℕ) := Nat.dvd_factorial m.pos (by omega)
  have h := ProfiniteInteger.castHom_proj hdvd a
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  simp only [ProfiniteInteger.proj_apply] at h
  rw [← h]
  rfl

theorem denseRange_natCast : DenseRange (Nat.cast : ℕ → ℤ̂) := fun a =>
  mem_closure_of_tendsto (tendsto_natCast a) (Eventually.of_forall fun _ => Set.mem_range_self _)

theorem mul_mem_of_isClosed' (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {x : ℤ̂}
    (hx : x ∈ H) (a : ℤ̂) : a * x ∈ H :=
  denseRange_natCast.induction_on a (hH.preimage (continuous_id.mul continuous_const))
    fun k => by
      show (k : ℤ̂) * x ∈ H
      rw [← nsmul_eq_mul]
      exact H.nsmul_mem hx k

def idealOfIsClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) : Ideal ℤ̂ where
  carrier := H
  add_mem' := H.add_mem
  zero_mem' := H.zero_mem
  smul_mem' a _ hx := mul_mem_of_isClosed' H hH hx a

noncomputable def primeIdempotent (q : Nat.Primes) : ℤ̂ :=
  ofPadics (Pi.single q 1)

theorem toPadicInt_primeIdempotent (q q' : Nat.Primes) :
    toPadicInt q' (primeIdempotent q) = Pi.single (M := fun q : Nat.Primes => ℤ_[q]) q 1 q' :=
  congrFun (toPadics_ofPadics _) q'

theorem mem_of_forall_toPadicInt (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {y : ℤ̂}
    (hy : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h = toPadicInt q y) : y ∈ H := by
  choose h hh hhy using hy
  let s : Finset Nat.Primes → ℤ̂ := fun F => ∑ q ∈ F, primeIdempotent q * h q
  have hs : ∀ F, s F ∈ H := fun F =>
    H.sum_mem fun q _ => mul_mem_of_isClosed' H hH (hh q) _
  have hcomp : ∀ (F : Finset Nat.Primes) (q' : Nat.Primes), toPadicInt q' (s F) = if q' ∈ F then toPadicInt q' y else 0 := by
    intro F q'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [s, map_sum, map_mul, toPadicInt_primeIdempotent]
    split_ifs with hq'
    · rw [Finset.sum_eq_single q', Pi.single_eq_same, one_mul, hhy]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb.symm, zero_mul]
      · intro h'; exact absurd hq' h'
    · refine Finset.sum_eq_zero fun b hb => ?_
      rw [Pi.single_eq_of_ne (by rintro rfl; exact hq' hb), zero_mul]
  have ht : Tendsto (fun F => toPadics (s F)) atTop (𝓝 (toPadics y)) := by
    rw [tendsto_pi_nhds]
    intro q'
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_ge_atTop {q'}] with F hF
    rw [toPadics_apply, hcomp, if_pos (Finset.singleton_subset_iff.1 hF), toPadics_apply]
  have ht' := (continuous_ofPadics.tendsto _).comp ht
  simp only [Function.comp_def, ofPadics_toPadics] at ht'
  exact hH.mem_of_tendsto ht' (Eventually.of_forall hs)

end ProfiniteInteger

end Cyclotomic

end GroundTheory.Global
