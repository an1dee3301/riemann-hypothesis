module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

theorem exists_adeles_haarMeasure_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  intro F _ _
  let Γ : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup
  have hdisc : DiscreteTopology Γ := by
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.1 hU
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have : ({0} : Set Γ) = ((↑) : Γ → AF F) ⁻¹' V := by
      ext ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := hx
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro h
        have : algebraMap F (AF F) y = 0 := congrArg Subtype.val h
        rw [this]; exact h0V
      · intro h
        have := hU0 y (hVU h)
        subst this
        ext; simp
    rw [this]
    exact hVo.preimage continuous_subtype_val
  letI : MeasurableSpace (Multiplicative (AF F)) := borel _
  haveI : BorelSpace (Multiplicative (AF F)) := ⟨rfl⟩
  haveI : SecondCountableTopology (Multiplicative (AF F)) := inferInstanceAs (SecondCountableTopology (AF F))
  haveI : DiscreteTopology (AddSubgroup.toSubgroup Γ) := hdisc
  obtain ⟨hc, D, hDm, hD⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain (AddSubgroup.toSubgroup Γ)
  haveI : Countable Γ := hc
  let D' : Set (AF F) := Multiplicative.ofAdd ⁻¹' D
  have hDm' : MeasurableSet D' := hDm
  have hfd : ∀ m : Measure (AF F), IsAddFundamentalDomain Γ D' m := by
    intro m
    refine IsAddFundamentalDomain.mk' hDm'.nullMeasurableSet ?_
    intro x
    obtain ⟨γ, hγ, huniq⟩ := hD (Multiplicative.ofAdd x)
    refine ⟨⟨γ.1.toAdd, γ.2⟩, hγ, ?_⟩
    intro g hg
    have := huniq ⟨Multiplicative.ofAdd g.1, g.2⟩ hg
    ext
    exact congrArg (fun s => Multiplicative.toAdd s.1) this
  let μ : Measure (AF F) := Measure.addHaar
  have hμD := hfd μ
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hfin : μ D' < ∞ := by
    calc μ D' ≤ μ (⋃ γ : Γ, (γ +ᵥ K) ∩ D') := by
          apply measure_mono
          intro d hd
          obtain ⟨x, hx⟩ := hKx d
          refine Set.mem_iUnion.2 ⟨⟨algebraMap F (AF F) x, x, rfl⟩, ?_, hd⟩
          refine ⟨_, hx, ?_⟩
          show algebraMap F (AF F) x + (d - algebraMap F (AF F) x) = d
          abel
      _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ D') := measure_iUnion_le _
      _ = μ K := (hμD.measure_eq_tsum K).symm
      _ < ∞ := hK.measure_lt_top
  have hpos : μ D' ≠ 0 := by
    intro h0
    have := hμD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter] at this
    have h2 : ∀ g : Γ, μ (g +ᵥ D') = 0 := fun g => by
      rw [measure_vadd]; exact h0
    simp only [h2, tsum_zero] at this
    exact (Measure.measure_univ_ne_zero.2 (NeZero.ne μ)) this
  refine ⟨(μ D')⁻¹ • μ, ?_, D', hDm', hfd _, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul (μ := μ) (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin.ne]

end GlobalTheory.SWQ
