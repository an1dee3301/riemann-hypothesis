module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Set Topology

theorem DiscreteFundamentalDomain.proof (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : DiscreteFundamentalDomain.Statement G := by
  classical
  intro μ Γ hΓ

  have hcount : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have h1t : (1 : G) ∈ t := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' t := by rw [hteq]; rfl
    simpa using this

  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_split (ht.mem_nhds h1t)
  let U : Set G := V ∩ Inv.inv ⁻¹' V
  have hUo : IsOpen U := hVo.inter (hVo.preimage continuous_inv)
  have hU1 : (1 : G) ∈ U := ⟨hV1, by simpa using hV1⟩
  have key : ∀ u ∈ U, ∀ w ∈ U, ∀ γ : Γ, (γ : G) = u * w⁻¹ → γ = 1 := by
    intro u hu w hw γ hγ
    have h : (γ : G) ∈ t := hγ ▸ hVV u hu.1 w⁻¹ hw.2
    have h' : γ ∈ ((↑) : Γ → G) ⁻¹' t := h
    rw [hteq] at h'
    exact h'

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : G => (fun x => x * g⁻¹) ⁻¹' U) (fun g => hUo.preimage (continuous_mul_const _))
  have hall : ∀ x : G, x ∈ ⋃ g : G, (fun x => x * g⁻¹) ⁻¹' U := fun x =>
    mem_iUnion.2 ⟨x, by simpa using hU1⟩
  have hTne : T.Nonempty := by
    have h := hall 1
    rw [← hTU] at h
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 h
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hTc.exists_eq_range hTne
  let A : ℕ → Set G := fun n => (fun x => x * (g n)⁻¹) ⁻¹' U
  have hAo : ∀ n, IsOpen (A n) := fun n => hUo.preimage (continuous_mul_const _)
  have hcover : ∀ x : G, ∃ n, x ∈ A n := by
    intro x
    have h := hall x
    rw [← hTU, hg] at h
    obtain ⟨_, ⟨n, rfl⟩, hx⟩ := mem_iUnion₂.1 h
    exact ⟨n, hx⟩

  let FD : Set G :=
    ⋃ n, A n ∩ ⋂ m, ⋂ (_ : m < n), ⋂ γ : Γ, (fun x => (γ : G) * x) ⁻¹' (A m)ᶜ
  have memFD : ∀ y, y ∈ FD ↔ ∃ n, y ∈ A n ∧ ∀ m < n, ∀ γ : Γ, (γ : G) * y ∉ A m := by
    intro y
    simp only [FD, mem_iUnion, mem_inter_iff, mem_iInter, mem_preimage, mem_compl_iff]
  have hmeas : MeasurableSet FD :=
    MeasurableSet.iUnion fun n => (hAo n).measurableSet.inter <|
      MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun γ =>
        (hAo m).measurableSet.compl.preimage (continuous_const_mul _).measurable

  have uniq : ∀ y, ∀ δ : Γ, y ∈ FD → (δ : G) * y ∈ FD → δ = 1 := by
    intro y δ hy hδy
    obtain ⟨n₁, hy₁, hy₂⟩ := (memFD y).1 hy
    obtain ⟨n₂, hδ₁, hδ₂⟩ := (memFD _).1 hδy
    rcases lt_trichotomy n₁ n₂ with h | rfl | h
    · exact absurd (by simpa using hy₁) (hδ₂ n₁ h δ⁻¹)
    · refine key _ hδ₁ _ hy₁ δ ?_
      group
    · exact absurd hδ₁ (hy₂ n₂ h δ)
  refine ⟨FD, hmeas, IsFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_⟩

  have hP : ∃ n, ∃ γ : Γ, (γ : G) * x ∈ A n := by
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, 1, by simpa using hn⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  have hγFD : (γ : G) * x ∈ FD := by
    refine (memFD _).2 ⟨Nat.find hP, hγ, fun m hm δ hδ => Nat.find_min hP hm ⟨δ * γ, ?_⟩⟩
    simpa [mul_assoc] using hδ
  refine ⟨γ, by simpa [Subgroup.smul_def] using hγFD, fun δ hδ => ?_⟩
  have hδ' : (δ : G) * x ∈ FD := by simpa [Subgroup.smul_def] using hδ
  have h1 := uniq _ (δ * γ⁻¹) hγFD (by simpa [mul_assoc] using hδ')
  simpa [mul_inv_eq_one] using h1

end GroundTheory.Heights₂.Heights.FiniteCovolume
