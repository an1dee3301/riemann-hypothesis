module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TateMain
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EpConvB

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors
open GroundTheory.Global GroundTheory.Automorphic

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) : ℝ :=
  if y.2 ∈ idealFiniteAdeles L then ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ else 0

theorem adeleWeight_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    0 ≤ adeleWeight L A y := by
  unfold adeleWeight
  split_ifs <;> positivity

theorem adeleWeight_le_one (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ 1 := by
  unfold adeleWeight
  split_ifs
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (homeomorphMixedSpace K y.1)]))
  · exact zero_le_one

theorem adeleWeight_mono {L L' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (L : FractionalIdeal (𝓞 K)⁰ K) ≤ L') (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ adeleWeight L' A y := by
  unfold adeleWeight
  by_cases h1 : y.2 ∈ idealFiniteAdeles L
  · have h2 : y.2 ∈ idealFiniteAdeles L' := idealFiniteAdeles_subset h h1
    simp only [if_pos h1, if_pos h2, le_refl]
  · rw [if_neg h1]
    split_ifs
    · positivity
    · exact le_rfl

@[simp] theorem adeleWeight_zero (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    adeleWeight L A (0 : 𝔸[K]) = 1 := by
  have h0 : (0 : 𝔸[K]).2 ∈ idealFiniteAdeles L := zero_mem _
  have h1 : homeomorphMixedSpace K (0 : 𝔸[K]).1 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  unfold adeleWeight
  rw [if_pos h0, h1]
  simp

theorem continuous_adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    Continuous (adeleWeight (K := K) L A) := by
  have hc : IsClopen ((idealFiniteAdeles L : AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles L), isOpen_idealFiniteAdeles L⟩
  have hc' : IsClopen {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L} := hc.preimage continuous_snd
  have hf : Continuous fun y : 𝔸[K] ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun y ↦ ?_
    have := norm_nonneg (homeomorphMixedSpace K y.1)
    positivity
  have : adeleWeight (K := K) L A = Set.indicator {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L}
      (fun y ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹) := by
    funext y
    simp only [adeleWeight, Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]
  exact hf.indicator (by rw [hc'.frontier_eq]; simp)
end

end GlobalTheory.CompanionTheory.EpConvB
