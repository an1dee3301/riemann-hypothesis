module

public import Mathlib
public import Formalism.PeriodIntegrals.UpqRep
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open    Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyChoice

open PI.UpqRep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in
theorem _root_.GlobalTheory.CayleyChoice.Kset_sub {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ _root_.PI.UpqRep.Kset ε) : g ∈ _root_.PI.UpqRep.UJset ε := by
  have hg' : g ∈ unitaryGroup (Fin n) ℂ ∧ g * _root_.PI.UpqRep.Jm ε = _root_.PI.UpqRep.Jm ε * g := hg
  obtain ⟨hu, hc⟩ := hg'
  show gᴴ * _root_.PI.UpqRep.Jm ε * g = _root_.PI.UpqRep.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
    (mem_unitaryGroup_iff').mp hu, Matrix.one_mul]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in
private theorem mul_mem_UJset_jet_harmonics {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ _root_.PI.UpqRep.UJset ε) (hb : b ∈ _root_.PI.UpqRep.UJset ε) : a * b ∈ _root_.PI.UpqRep.UJset ε := by
  have ha' : aᴴ * _root_.PI.UpqRep.Jm ε * a = _root_.PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * _root_.PI.UpqRep.Jm ε * b = _root_.PI.UpqRep.Jm ε := hb
  show (a * b)ᴴ * _root_.PI.UpqRep.Jm ε * (a * b) = _root_.PI.UpqRep.Jm ε
  rw [conjTranspose_mul, show bᴴ * aᴴ * _root_.PI.UpqRep.Jm ε * (a * b) = bᴴ * (aᴴ * _root_.PI.UpqRep.Jm ε * a) * b by
    simp only [Matrix.mul_assoc], ha', hb']

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in
private theorem isKTypeOf_map_of_intertwining {σ₁ σ₂ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (e : H ≃ₗ[ℂ] H)
    (he : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ₂ k (e x) = e (σ₁ k x)) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : _root_.PI.UpqRep.IsKTypeOf ε σ₁ μ S) : _root_.PI.UpqRep.IsKTypeOf ε σ₂ μ (S.map (e : H →ₗ[ℂ] H)) := by
  obtain ⟨hfin, hinv, hirr, ⟨v, hvS, hv0, hvw⟩, hmax⟩ := hS
  have inv_map : ∀ T : Submodule ℂ H, _root_.PI.UpqRep.IsKStableOn ε σ₁ T →
      _root_.PI.UpqRep.IsKStableOn ε σ₂ (T.map (e : H →ₗ[ℂ] H)) := by
    intro T hT k hk y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨σ₁ k x, hT k hk x hx, (he k hk x).symm⟩
  have inv_comap : ∀ T : Submodule ℂ H, _root_.PI.UpqRep.IsKStableOn ε σ₂ T →
      _root_.PI.UpqRep.IsKStableOn ε σ₁ (T.comap (e : H →ₗ[ℂ] H)) := by
    intro T hT k hk x hx
    show e (σ₁ k x) ∈ T
    rw [← he k hk x]
    exact hT k hk _ hx
  have wt : ∀ (ν : Fin n → ℝ) (x : H), _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₁ ν x →
      _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₂ ν (e x) := by
    intro ν x hx θ hθ
    rw [he _ hθ, hx θ hθ, map_smul]
  have wt' : ∀ (ν : Fin n → ℝ) (x : H), _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₂ ν (e x) →
      _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₁ ν x := by
    intro ν x hx θ hθ
    apply e.injective
    rw [← he _ hθ, hx θ hθ, map_smul]
  refine ⟨?_, inv_map S hinv, ?_, ⟨e v, ⟨v, hvS, rfl⟩, by simpa using hv0, wt μ v hvw⟩, ?_⟩
  · haveI := hfin
    infer_instance
  · intro T hT hTinv
    have hle : T.comap (e : H →ₗ[ℂ] H) ≤ S := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hT hx
      rwa [← e.injective hxy]
    rcases hirr _ hle (inv_comap T hTinv) with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have hy' : e.symm y ∈ T.comap (e : H →ₗ[ℂ] H) := by simpa using hy
      rw [h, Submodule.mem_bot] at hy'
      simpa using congrArg e hy'
    · right
      refine le_antisymm hT ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← h] at hx
      exact hx
  · intro ν y hy hy0 hyw
    obtain ⟨x, hx, rfl⟩ := hy
    exact hmax ν x hx (by rintro rfl; simp at hy0) (wt' ν x hyw)


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in
theorem _root_.GlobalTheory.CayleyChoice.isDS_conj {lam : Fin n → ℝ} (hσ : _root_.PI.UpqRep.IsDS ε lam σ)
    {u u' : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ _root_.PI.UpqRep.UJset ε) (hu' : u' ∈ _root_.PI.UpqRep.UJset ε) (h1 : u * u' = 1) :
    _root_.PI.UpqRep.IsDS ε lam (fun g => σ (u' * g * u)) := by
  obtain ⟨hc, hnt, ⟨⟨h1σ, hmul⟩, hiso, hcont⟩, hirr, hL2, ⟨S, hS⟩, hmin⟩ := hσ
  have hu'u : u' * u = 1 := mul_eq_one_comm.mp h1
  have conj_mem : ∀ {g}, g ∈ _root_.PI.UpqRep.UJset ε → u' * g * u ∈ _root_.PI.UpqRep.UJset ε := fun hg =>
    mul_mem_UJset_jet_harmonics (mul_mem_UJset_jet_harmonics hu' hg) hu
  have hAB : ∀ x, σ u (σ u' x) = x := by
    intro x
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hu _ hu', h1, h1σ]
    rfl
  have hBA : ∀ x, σ u' (σ u x) = x := by
    intro x
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hu' _ hu, hu'u, h1σ]
    rfl
  have hconj : ∀ g ∈ _root_.PI.UpqRep.UJset ε, ∀ x, σ (u' * g * u) x = σ u' (σ g (σ u x)) := by
    intro g hg x
    rw [hmul _ (mul_mem_UJset_jet_harmonics hu' hg) _ hu, hmul _ hu' _ hg]
    rfl
  have hinner : ∀ x y, ⟪σ u x, σ u y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    let L : H →ₗᵢ[ℂ] H := ⟨(σ u : H →ₗ[ℂ] H), hiso u hu⟩
    exact L.inner_map_map x y
  let e : H ≃ₗ[ℂ] H :=
    { toLinearMap := (σ u' : H →ₗ[ℂ] H)
      invFun := σ u
      left_inv := hAB
      right_inv := hBA }
  have he : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ (u' * k * u) (e x) = e (σ k x) := by
    intro k hk x
    show σ (u' * k * u) (σ u' x) = σ u' (σ k x)
    rw [hconj k (_root_.GlobalTheory.CayleyChoice.Kset_sub hk), hAB]
  have he' : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ k (e.symm x) = e.symm (σ (u' * k * u) x) := by
    intro k hk x
    show σ k (σ u x) = σ u (σ (u' * k * u) x)
    rw [hconj k (_root_.GlobalTheory.CayleyChoice.Kset_sub hk), hAB]
  refine ⟨hc, hnt, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨_, isKTypeOf_map_of_intertwining e he hS⟩, ?_⟩
  · show σ (u' * 1 * u) = 1
    rw [Matrix.mul_one, hu'u, h1σ]
  · intro a ha b hb
    show σ (u' * (a * b) * u) = σ (u' * a * u) ∘SL σ (u' * b * u)
    rw [← hmul _ (conj_mem ha) _ (conj_mem hb)]
    congr 1
    rw [show u' * a * u * (u' * b * u) = u' * a * (u * u') * b * u by
      simp only [Matrix.mul_assoc], h1, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  · intro g hg v
    exact hiso _ (conj_mem hg) v
  · intro v
    exact (hcont v).comp ((continuous_const.mul continuous_id).mul continuous_const).continuousOn
      (fun g hg => conj_mem hg)
  · intro T hTc hTinv
    have hT'c : IsClosed (↑(T.comap (σ u' : H →ₗ[ℂ] H)) : Set H) :=
      hTc.preimage (σ u').continuous
    have hT'inv : ∀ g ∈ _root_.PI.UpqRep.UJset ε, ∀ x ∈ T.comap (σ u' : H →ₗ[ℂ] H),
        σ g x ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
      intro g hg x hx
      have hx' : σ u' x ∈ T := hx
      show σ u' (σ g x) ∈ T
      have := hTinv g hg (σ u' x) hx'
      rw [show σ u' (σ g x) = σ (u' * g * u) (σ u' x) by rw [hconj g hg, hAB]]
      exact this
    rcases hirr _ hT'c hT'inv with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have hmem : σ u y ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
        show σ u' (σ u y) ∈ T
        rwa [hBA]
      rw [h, Submodule.mem_bot] at hmem
      rw [Submodule.mem_bot, ← hBA y, hmem, map_zero]
    · right
      rw [eq_top_iff]
      intro y _
      have hmem : σ u y ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
        rw [h]
        exact Submodule.mem_top
      have hmem' : σ u' (σ u y) ∈ T := hmem
      rwa [hBA] at hmem'
  · intro v w
    have key := hL2 (σ u v) (σ u w)
    convert key using 1
    funext g
    have hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.PI.UpqRep.UJset ε := g.2
    show ⟪w, σ (u' * _ * u) v⟫_ℂ = ⟪σ u w, σ _ (σ u v)⟫_ℂ
    rw [hconj _ hg, ← hinner, hAB]
  · intro μ T hT
    exact hmin μ _ (isKTypeOf_map_of_intertwining e.symm he' hT)



end GlobalTheory.CayleyChoice
