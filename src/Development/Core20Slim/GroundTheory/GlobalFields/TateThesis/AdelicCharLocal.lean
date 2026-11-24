module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Batteries.Classes.RatCast
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct FourierTransform

noncomputable section

variable {K : Type*} [Field K] [NumberField K]


open Classical in
def finiteAdeleSingleAdd (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →+ FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.single
    (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletionIntegers K) v x
  map_zero' := Subtype.ext (Pi.single_zero (M := fun u : HeightOneSpectrum (𝓞 K) =>
    u.adicCompletion K) v)
  map_add' x y := Subtype.ext (Pi.single_add (f := fun u : HeightOneSpectrum (𝓞 K) =>
    u.adicCompletion K) v x y)

open Classical in
theorem finiteAdeleSingleAdd_apply (v u : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingleAdd v x u =
      Pi.single (M := fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) v x u := rfl

@[simp]
theorem finiteAdeleSingleAdd_apply_self (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingleAdd v x v = x := by
  classical
  rw [finiteAdeleSingleAdd_apply]
  exact Pi.single_eq_same v x

theorem finiteAdeleSingleAdd_apply_of_ne {v u : HeightOneSpectrum (𝓞 K)} (h : u ≠ v)
    (x : v.adicCompletion K) : finiteAdeleSingleAdd v x u = 0 := by
  classical
  rw [finiteAdeleSingleAdd_apply]
  exact Pi.single_eq_of_ne h x

theorem continuous_finiteAdeleSingleAdd (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteAdeleSingleAdd (K := K) v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by
    simp
  let g : v.adicCompletion K → Πʳ w : HeightOneSpectrum (𝓞 K),
      [w.adicCompletion K, w.adicCompletionIntegers K]_[Filter.principal {v}ᶜ] :=
    fun x ↦ ⟨Pi.single v x, Filter.eventually_principal.2 fun w hw ↦ by
      rw [Pi.single_eq_of_ne hw x]
      exact zero_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single v)
  have hfg : (finiteAdeleSingleAdd (K := K) v : v.adicCompletion K → FiniteAdeleRing (𝓞 K) K) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

def finiteAdeleInr : FiniteAdeleRing (𝓞 K) K →+ 𝔸[K] :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
    FiniteAdeleRing (𝓞 K) K →+ InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

@[simp] theorem finiteAdeleInr_fst (a : FiniteAdeleRing (𝓞 K) K) : (finiteAdeleInr a).1 = 0 :=
  rfl

@[simp] theorem finiteAdeleInr_snd (a : FiniteAdeleRing (𝓞 K) K) : (finiteAdeleInr a).2 = a :=
  rfl

def finitePlaceIncl (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K →+ 𝔸[K] :=
  finiteAdeleInr.comp (finiteAdeleSingleAdd v)

theorem finitePlaceIncl_apply (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finitePlaceIncl v x = finiteAdeleInr (finiteAdeleSingleAdd v x) := rfl

theorem continuous_finitePlaceIncl (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finitePlaceIncl (K := K) v) :=
  continuous_const.prodMk (continuous_finiteAdeleSingleAdd v)


open Classical in
def infinitePlaceIncl (w : InfinitePlace K) : w.Completion →+ 𝔸[K] :=
  ((AddMonoidHom.single (fun u : InfinitePlace K => u.Completion) w).prod 0 :
    w.Completion →+ InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)


@[simp] theorem infinitePlaceIncl_snd (w : InfinitePlace K) (z : w.Completion) :
    (infinitePlaceIncl w z).2 = 0 := rfl

def infiniteAdeleInl : InfiniteAdeleRing K →+ 𝔸[K] :=
  (AddMonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
    InfiniteAdeleRing K →+ InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

@[simp] theorem infiniteAdeleInl_fst (x : InfiniteAdeleRing K) : (infiniteAdeleInl x).1 = x :=
  rfl

@[simp] theorem infiniteAdeleInl_snd (x : InfiniteAdeleRing K) : (infiniteAdeleInl x).2 = 0 :=
  rfl

theorem infiniteAdeleInl_add_finiteAdeleInr (x : 𝔸[K]) :
    infiniteAdeleInl x.1 + finiteAdeleInr x.2 = x := by
  have h : infiniteAdeleInl x.1 + finiteAdeleInr x.2 = (x.1 + 0, 0 + x.2) := rfl
  simpa using h


variable (K) in
def localAdelicChar (v : HeightOneSpectrum (𝓞 K)) : AddChar (v.adicCompletion K) Circle :=
  (adelicChar K).compAddMonoidHom (finitePlaceIncl v)



theorem localAdelicChar_apply (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) :
    localAdelicChar K v y = adelicChar K (finitePlaceIncl v y) := rfl


theorem continuous_localAdelicChar (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localAdelicChar K v) :=
  (continuous_adelicChar (K := K)).comp (continuous_finitePlaceIncl v)




theorem addChar_map_finsetSum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A Circle)
    (s : Finset ι) (f : ι → A) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]


theorem coe_sub_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (a b : K) :
    ((a - b : K) : v.adicCompletion K) = (a : v.adicCompletion K) - (b : v.adicCompletion K) := by
  have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
    fun z => by simp [algebraMap_adicCompletion]
  rw [hc, hc, hc, map_sub]

theorem exists_sub_mem_adicCompletionIntegers_and_forall_ne (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    ∃ k : K, y - k ∈ v.adicCompletionIntegers K ∧
      ∀ u ≠ v, (k : u.adicCompletion K) ∈ u.adicCompletionIntegers K := by
  classical
  have hU : IsOpen {z : v.adicCompletion K | y - z ∈ v.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU ⟨y, by simp⟩
  obtain ⟨k, hkS, hkn⟩ := exists_valuation_sub_le_one {v} (fun _ => z)
  refine ⟨k, ?_, fun u hu => ?_⟩
  · have h1 := (coe_mem_adicCompletionIntegers_iff v (k - z)).mpr (hkS v (Finset.mem_singleton_self v))
    have h2 : y - (k : v.adicCompletion K) =
        (y - (z : v.adicCompletion K)) - ((k - z : K) : v.adicCompletion K) := by
      rw [coe_sub_adicCompletion]
      ring
    rw [h2]
    have hz' : y - (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K := hz
    exact sub_mem hz' h1
  · exact (coe_mem_adicCompletionIntegers_iff u k).mpr (hkn u (by simpa using hu))

theorem localAdelicChar_eq_one_of_mem {v : HeightOneSpectrum (𝓞 K)} {y : v.adicCompletion K}
    (hy : y ∈ localInvDifferent v) : localAdelicChar K v y = 1 := by
  rw [localAdelicChar_apply, adelicChar_of_mem_invDifferentAdeles]
  · simp [finitePlaceIncl_apply]
  · refine mem_invDifferentAdeles.mpr fun u => ?_
    rw [finitePlaceIncl_apply, finiteAdeleInr_snd]
    by_cases hu : u = v
    · subst hu
      rwa [finiteAdeleSingleAdd_apply_self]
    · rw [finiteAdeleSingleAdd_apply_of_ne hu]
      exact zero_mem _

theorem localAdelicChar_eq (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) {k : K}
    (hk : y - k ∈ localInvDifferent v)
    (hk' : ∀ u ≠ v, (k : u.adicCompletion K) ∈ localInvDifferent u) :
    localAdelicChar K v y = 𝐞 (Algebra.trace ℚ K k) := by
  rw [localAdelicChar_apply, adelicChar_eq (k := k)]
  · rw [finitePlaceIncl_apply, finiteAdeleInr_fst, zero_sub, map_neg (infiniteTrace K), neg_neg,
      infiniteTrace_algebraMap]
  · intro u
    show finiteAdeleSingleAdd v y u - (k : u.adicCompletion K) ∈ localInvDifferent u
    by_cases hu : u = v
    · subst hu
      rwa [finiteAdeleSingleAdd_apply_self]
    · rw [finiteAdeleSingleAdd_apply_of_ne hu, zero_sub]
      exact neg_mem (hk' u hu)

theorem localAdelicChar_coe (v : HeightOneSpectrum (𝓞 K)) {k : K}
    (hk' : ∀ u ≠ v, (k : u.adicCompletion K) ∈ localInvDifferent u) :
    localAdelicChar K v k = 𝐞 (Algebra.trace ℚ K k) :=
  localAdelicChar_eq v _ (by rw [sub_self]; exact zero_mem _) hk'

theorem forall_localAdelicChar_mul_eq_one_iff (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) :
    (∀ a ∈ v.adicCompletionIntegers K, localAdelicChar K v (a * x) = 1) ↔
      x ∈ localInvDifferent v := by
  refine ⟨fun h => ?_, fun hx a ha => localAdelicChar_eq_one_of_mem
    (mul_mem_localInvDifferent ha hx)⟩
  obtain ⟨k, hk, hk'⟩ := exists_sub_mem_adicCompletionIntegers_and_forall_ne v x
  have htr : ∀ a : 𝓞 K,
      Algebra.trace ℚ K (k * algebraMap (𝓞 K) K a) ∈ (algebraMap ℤ ℚ).range := by
    intro a
    have hb' : ∀ u ≠ v, ((k * algebraMap (𝓞 K) K a : K) : u.adicCompletion K) ∈
        localInvDifferent u := fun u hu => mem_localInvDifferent_of_mem (by
      rw [coe_mul_adicCompletion]
      exact mul_mem (hk' u hu) (coe_algebraMap_mem_adicCompletionIntegers u a))
    have h1 := localAdelicChar_coe v hb'
    have hbx : ((k * algebraMap (𝓞 K) K a : K) : v.adicCompletion K) =
        ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) * x -
          ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) * (x - k) := by
      rw [coe_mul_adicCompletion]
      ring
    rw [hbx, AddChar.map_sub_eq_div, h _ (coe_algebraMap_mem_adicCompletionIntegers v a),
      localAdelicChar_eq_one_of_mem (mul_mem_localInvDifferent
        (coe_algebraMap_mem_adicCompletionIntegers v a) (mem_localInvDifferent_of_mem hk)),
      div_one, eq_comm, fourierChar_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by exact_mod_cast hn.symm⟩
  have hk_mem := (forall_mul_mem_iff_forall_trace_mem K k).mpr htr
  intro y hy
  obtain ⟨z, hz⟩ := hk_mem y hy
  have : x * ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) =
      ((k * algebraMap (𝓞 K) K y : K) : v.adicCompletion K) +
        (x - k) * ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) := by
    rw [coe_mul_adicCompletion]
    ring
  rw [this, ← hz]
  exact add_mem (coe_algebraMap_mem_adicCompletionIntegers v z)
    (mul_mem hk (coe_algebraMap_mem_adicCompletionIntegers v y))

theorem forall_localAdelicChar_eq_one_iff_le (v : HeightOneSpectrum (𝓞 K))
    (M : AddSubgroup (v.adicCompletion K))
    (hM : ∀ a ∈ v.adicCompletionIntegers K, ∀ x ∈ M, a * x ∈ M) :
    (∀ x ∈ M, localAdelicChar K v x = 1) ↔ M ≤ localInvDifferent v :=
  ⟨fun h x hx => (forall_localAdelicChar_mul_eq_one_iff v x).mp fun a ha => h _ (hM a ha x hx),
    fun h _ hx => localAdelicChar_eq_one_of_mem (h hx)⟩


end

end GroundTheory.Global
