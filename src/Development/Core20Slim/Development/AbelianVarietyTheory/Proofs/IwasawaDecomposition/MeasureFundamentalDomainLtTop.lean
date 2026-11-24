module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Formalism.HermitianLattices.StatementMass
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Order.Real

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselConvDefinite

theorem isAniso_of_isDefinite {D : D7} (A : HSp D) (hs : A.SigOK) (hd : A.IsDefinite) : IsAniso A := by
  rw [GlobalTheory.BesselCompare.isAniso_iff]
  intro v hv
  by_contra hne
  have hc := D.sp.cm.cmUnram
  have := hc.1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  rcases hd τ with h | h
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_pos_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_neg_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this


open Pointwise in
theorem measure_fundamentalDomain_lt_top {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ), ⟨k, hk, e.symm⟩, hg⟩
  calc μ F ≤ μ (⋃ γ : Γ, ((γ • K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

section Conj

open GlobalTheory.BesselCompare

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}








end Conj


end GlobalTheory.BesselConvDefinite
