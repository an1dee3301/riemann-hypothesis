module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

namespace PI.AddIntG.Wk

def SerS {K : Type*} [CommRing K] (S : Subring K) (σ : Type*) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map S.subtype).range

theorem mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by
  rw [SerS, RingHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e g).2
  · intro h
    refine ⟨(fun e => ⟨MvPowerSeries.coeff e f, h e⟩ : MvPowerSeries σ S), ?_⟩
    ext e
    rfl

theorem SerS_eq_map {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (hf : f ∈ SerS S σ) : ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f :=
  RingHom.mem_range.mp hf

theorem constantCoeff_lift {K : Type*} [CommRing K] (S : Subring K) {σ : Type*}
    (g : MvPowerSeries σ S) {c : S} (h : MvPowerSeries.constantCoeff (MvPowerSeries.map S.subtype g) = (c : K)) :
    MvPowerSeries.constantCoeff g = c := by
  apply Subtype.ext
  rw [← h]
  simp

theorem inv_mem_SerS {K : Type*} [Field K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (h0 : MvPowerSeries.constantCoeff f = 1) (hf : f ∈ SerS S σ) : f⁻¹ ∈ SerS S σ := by
  obtain ⟨g, rfl⟩ := SerS_eq_map S hf
  have hg : MvPowerSeries.constantCoeff g = 1 :=
    constantCoeff_lift S g (c := 1) (by rw [h0]; rfl)
  have h1 : g * MvPowerSeries.invOfUnit g 1 = 1 :=
    MvPowerSeries.mul_invOfUnit g 1 (by rw [hg]; rfl)
  rw [SerS, RingHom.mem_range]
  refine ⟨MvPowerSeries.invOfUnit g 1, ?_⟩
  symm
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one (by rw [h0]; exact one_ne_zero), ← map_mul, mul_comm, h1,
    map_one]

theorem mvsubst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ K} {f : MvPowerSeries σ K} (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, a i ∈ SerS S τ) (hf : f ∈ SerS S σ) : MvPowerSeries.subst a f ∈ SerS S τ := by
  classical
  rw [mem_SerS] at hf ⊢
  intro e
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  have hterm : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) ∈ S := by
    intro d
    rw [smul_eq_mul]
    refine S.mul_mem (hf d) ?_
    have hp : (d.prod fun s n => a s ^ n) ∈ SerS S τ :=
      Subring.prod_mem _ fun s _ => Subring.pow_mem _ (ha s) _
    exact (mem_SerS S _).1 hp e
  rw [finsum_def]
  split_ifs
  · exact Subring.sum_mem _ fun i _ => hterm _
  · exact S.zero_mem

theorem subst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {τ : Type*} {a : MvPowerSeries τ K}
    {f : PowerSeries K} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : a ∈ SerS S τ)
    (hf : (f : MvPowerSeries Unit K) ∈ SerS S Unit) : PowerSeries.subst a f ∈ SerS S τ :=
  mvsubst_mem_SerS S (a := fun _ : Unit => a) (fun _ => ha0) (fun _ => ha) hf

end PI.AddIntG.Wk
