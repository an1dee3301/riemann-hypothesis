module

public import Mathlib
public import Init.Core
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

theorem UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulLeftInvariant] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      (μ : Set G → ENNReal) (↑K : Set G) ≠ ⊤ →
        ∀ {S : Set G},
          IsCompact S →
            (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
              ∃ (t : Finset (G ⧸ K)),
                (∀ Q ∈ t, Quotient.out Q ∈ S) ∧
                  ∀ (f : G → ℂ),
                    (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
                      ∫ (g : G) in S, f g ∂μ = ∑ Q ∈ t, f (Quotient.out Q) * (↑(μ.real (↑K : Set G)) : ℂ) := by
  intro G _ _ _ _ _ μ _ K hK hμ S hS hSK
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  let C : G ⧸ K → Set G := fun Q => (fun g => (Quotient.out Q)⁻¹ * g) ⁻¹' (K : Set G)
  have hC : ∀ Q g, g ∈ C Q ↔ (QuotientGroup.mk g : G ⧸ K) = Q := by
    intro Q g
    have h := QuotientGroup.eq (s := K) (a := Quotient.out Q) (b := g)
    rw [QuotientGroup.out_eq'] at h
    rw [eq_comm, h]
    rfl
  have hout : ∀ Q ∈ hfin.toFinset, Quotient.out Q ∈ S := by
    intro Q hQ
    obtain ⟨s, hs, rfl⟩ := hfin.mem_toFinset.1 hQ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hk]
    exact hSK s hs k k.2
  have hmeas : ∀ Q, MeasurableSet (C Q) := fun Q =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ Q, μ (C Q) = μ K := fun Q => MeasureTheory.measure_preimage_mul μ _ _
  have hU : S = ⋃ Q ∈ hfin.toFinset, C Q := by
    ext g
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hg
      exact ⟨_, hfin.mem_toFinset.2 ⟨g, hg, rfl⟩, (hC _ g).2 rfl⟩
    · rintro ⟨Q, hQ, hg⟩
      have := hSK _ (hout Q hQ) _ hg
      simpa using this
  refine ⟨hfin.toFinset, hout, fun f hf => ?_⟩
  have hconst : ∀ Q ∈ hfin.toFinset, Set.EqOn f (fun _ => f (Quotient.out Q)) (C Q) := by
    intro Q hQ g hg
    have := hf _ (hout Q hQ) _ hg
    simpa using this
  have hsplit : ∫ g in ⋃ Q ∈ hfin.toFinset, C Q, f g ∂μ
      = ∑ Q ∈ hfin.toFinset, ∫ g in C Q, f g ∂μ := by
    refine MeasureTheory.integral_biUnion_finset _ (fun Q _ => hmeas Q) ?_ ?_
    · intro Q _ R _ hQR
      refine Set.disjoint_left.2 fun g h1 h2 => hQR ?_
      rw [← (hC Q g).1 h1, (hC R g).1 h2]
    · intro Q hQ
      refine (MeasureTheory.integrableOn_congr_fun (hconst Q hQ) (hmeas Q)).2 ?_
      exact MeasureTheory.integrableOn_const (by rw [hμC]; exact hμ)
  rw [← hU] at hsplit
  rw [hsplit]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [MeasureTheory.setIntegral_congr_fun (hmeas Q) (hconst Q hQ),
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, hμC,
    MeasureTheory.measureReal_def, Complex.real_smul, mul_comm]
