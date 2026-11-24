module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.WeilCont

variable (F : Type) [Field F] [NumberField F] {κ : Type}

def adeleJoin (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem pureA_adeleJoin (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (adeleJoin F x y) = f x * g y := by
  simp only [GlobalTheory.WeilM.pureA, adeleJoin, RingEquiv.apply_symm_apply]

theorem exists_slice [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ x, s x = Φ (adeleJoin F x y) := by
  unfold GlobalTheory.WeilM.schA at hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    exact ⟨g y • f, fun x => by rw [smul_apply, pureA_adeleJoin, smul_eq_mul, mul_comm]⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    exact ⟨s1 + s2, fun x => by rw [add_apply, hs1, hs2]; rfl⟩
  | smul c Φ _ h =>
    obtain ⟨s, hs⟩ := h
    exact ⟨c • s, fun x => by rw [smul_apply, hs]; rfl⟩

theorem isContOn_of_local [Fintype κ] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] {G : Type} [Group G] [TopologicalSpace G]
    {om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)}
    (hfin : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ p0 : G, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (hsl : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      ∃ s : G → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Continuous s ∧ ∀ p x, s p x = om p Φ (adeleJoin F x y)) :
    GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass F) om := by
  intro l hl φ hφ
  change φ ∈ GlobalTheory.WeilM.schA F κ at hφ
  change ∀ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (GlobalTheory.WeilM.pureA F f g) = T f at hl
  rw [continuous_iff_continuousAt]
  intro p0
  obtain ⟨N, hN, m, g, y, hgSB, hgy, hrep⟩ := hfin φ hφ p0
  choose T hT using fun i => hl (g i) (hgSB i)
  choose s hs hsx using fun j => hsl φ hφ (y j)
  have hcont : Continuous fun p => ∑ i, T i (s i p) :=
    continuous_finsetSum _ (fun i _ => (T i).continuous.comp (hs i))
  refine hcont.continuousAt.congr ?_
  filter_upwards [hN] with p hp
  obtain ⟨f, hf⟩ := hrep p hp
  have hfs : ∀ j, f j = s j p := by
    intro j
    ext x
    rw [hsx, hf, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [pureA_adeleJoin, hgy j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [pureA_adeleJoin, hgy i j, if_neg hij, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hT, hfs])

end GlobalTheory.WeilCont

end
