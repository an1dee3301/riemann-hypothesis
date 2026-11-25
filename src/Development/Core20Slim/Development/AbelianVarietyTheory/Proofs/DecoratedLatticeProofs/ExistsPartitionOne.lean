module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatPartition

theorem finite_ratW_mem {D : D7} (A T : HSp D) {C : Set (WO A T)} (hC : IsCompact C) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ C}.Finite := by
  obtain ⟨i1, -, -, i4, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i4; haveI := i5
  haveI : T1Space (Mx D T.rank A.rank) := @T2Space.t1Space _ _ i4
  have hLc : IsClosed (ratMx D T.rank A.rank : Set (Mx D T.rank A.rank)) := AddSubgroup.isClosed_of_discrete
  let φ : Matrix (Fin T.rank) (Fin A.rank) D.host.E → ratMx D T.rank A.rank := fun γ => ⟨ratW T A γ, γ, rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h)
  have hs : IsCompact ((↑) ⁻¹' C : Set (ratMx D T.rank A.rank)) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact hC.inter_right hLc
  exact (hs.finite_of_discrete.preimage (f := φ) hφ.injOn : _)

theorem exists_partition_one : ∀ (D : D7) (A T : HSp D), ∃ χ : WO A T → ℝ, Continuous χ ∧ HasCompactSupport χ ∧
    (∀ u, 0 ≤ χ u) ∧ ∀ u, HasSum (fun γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E => χ (ratW T A γ + u)) 1 := by
  intro D A T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i2; haveI := i4
  haveI : RegularSpace (Mx D T.rank A.rank) := IsTopologicalAddGroup.regularSpace _
  haveI : ContinuousSub (Mx D T.rank A.rank) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  have hS : IsCompact (tsupport f) := hfc
  let g : Matrix (Fin T.rank) (Fin A.rank) D.host.E → WO A T → ℝ := fun γ u => f (ratW T A γ + u)
  have hgc : ∀ γ, Continuous (g γ) := fun γ => f.continuous.comp (continuous_const_add (ratW T A γ : WO A T))
  have hfin : ∀ N : Set (WO A T), IsCompact N → {γ | (Function.support (g γ) ∩ N).Nonempty}.Finite := by
    intro N hN
    refine (finite_ratW_mem A T ((hS.prod hN).image (continuous_fst.sub continuous_snd))).subset ?_
    rintro γ ⟨u, hu, huN⟩
    exact ⟨(ratW T A γ + u, u), ⟨subset_tsupport _ hu, huN⟩, add_sub_cancel_right _ _⟩
  have hlf : LocallyFinite fun γ => Function.support (g γ) := by
    intro u
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds u
    exact ⟨N, hN, hfin N hNc⟩
  have hpt : ∀ u, (Function.support fun γ => g γ u).Finite := by
    intro u
    refine (hfin {u} isCompact_singleton).subset ?_
    intro γ hγ
    exact ⟨u, hγ, rfl⟩
  let s : WO A T → ℝ := fun u => ∑ᶠ γ, g γ u
  have hs_cont : Continuous s := continuous_finsum hgc hlf
  have hg0 : ∀ γ u, 0 ≤ g γ u := fun γ u => (hf01 _).1
  have hs1 : ∀ u, 1 ≤ s u := by
    intro u
    obtain ⟨x, ⟨γ, rfl⟩, hx⟩ := hKc u
    have h1 : g γ u = 1 := hf1 hx
    rw [← h1]
    exact single_le_finsum γ (hpt u) (fun j => hg0 j u)
  have hs_inv : ∀ γ₀ u, s (ratW T A γ₀ + u) = s u := by
    intro γ₀ u
    have e : ∀ γ, g γ (ratW T A γ₀ + u) = g (γ + γ₀) u := by
      intro γ
      simp only [g, ratW]
      rw [Matrix.map_add _ (map_add (incA D)) γ γ₀, add_assoc]
    simp only [s, e]
    exact finsum_comp_equiv (Equiv.addRight γ₀) (f := fun γ => g γ u)
  have hpos : ∀ u, 0 < s u := fun u => zero_lt_one.trans_le (hs1 u)
  refine ⟨fun u => f u * (s u)⁻¹, f.continuous.mul (hs_cont.inv₀ fun u => (hpos u).ne'), hfc.mul_right,
    fun u => mul_nonneg (hf01 u).1 (inv_nonneg.2 (hpos u).le), fun u => ?_⟩
  have e : (fun γ => f (ratW T A γ + u) * (s (ratW T A γ + u))⁻¹) = fun γ => g γ u * (s u)⁻¹ := by
    funext γ
    rw [hs_inv]
  simp only [e]
  have h : HasSum (fun γ => g γ u) (∑ γ ∈ (hpt u).toFinset, g γ u) :=
    hasSum_sum_of_ne_finset_zero (fun γ hγ => by simpa using hγ)
  rw [← finsum_eq_sum _ (hpt u)] at h
  have h2 := h.mul_right (s u)⁻¹
  rwa [mul_inv_cancel₀ (hpos u).ne'] at h2

end GlobalTheory.RatPartition

end
