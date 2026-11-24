module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Formalism.LocalRingCardinality.DataHost
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
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SkewVol

variable (D : D7) (ρ : ℕ)

def skewPart (x : Mx D ρ ρ) : Mx D ρ ρ := half D • (x - adj x)

variable {D ρ}

theorem skewPart_mem (x : Mx D ρ ρ) : skewPart D ρ x ∈ skewA D ρ := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {c : Mx D ρ ρ} (hc : c ∈ skewA D ρ) : skewPart D ρ c = c := by
  rw [skewPart, (mem_skewA).1 hc, sub_neg_eq_add, smul_add, half_smul_add]

theorem skewPart_add (x y : Mx D ρ ρ) : skewPart D ρ (x + y) = skewPart D ρ x + skewPart D ρ y := by
  rw [skewPart, skewPart, skewPart, adj_add, add_sub_add_comm, smul_add]

theorem skewPart_rat {x : Mx D ρ ρ} (hx : x ∈ ratMx D ρ ρ) : skewPart D ρ x ∈ ratMx D ρ ρ := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ - γᴴ), ?_⟩
  rw [rat_smul, rat_sub, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPart D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  show Continuous fun x => half D • (x - adj x) from (continuous_id.sub continuous_adj).const_smul (half D)

theorem isClosed_skewA : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) :=
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.2.1
  isClosed_eq continuous_adj continuous_neg

theorem isCoLat_skew :
    GlobalTheory.CuspGeneric.IsCoLat ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D ρ ρ
  refine ⟨?_, ?_⟩
  · let φ : (ratMx D ρ ρ).addSubgroupOf (skewA D ρ) → ratMx D ρ ρ := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D ρ ρ → skewA D ρ := fun x => ⟨skewPart D ρ x, skewPart_mem x⟩
    have hP : Continuous P := continuous_skewPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_addSubgroupOf.2 (skewPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change skewPart D ρ (γ + x.1) = skewPart D ρ γ + x.1
    rw [skewPart_add, skewPart_of_mem x.2]

theorem exists_haar_covol_one : ∀ (D : D7) (ρ : ℕ), ∃ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure ∧ SFinite lC ∧ IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC ∧ lC 𝓒 = 1 := by
  intro D ρ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (skewA D ρ) := (isClosed_skewA (D := D) (ρ := ρ)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (skewA D ρ) _ isCoLat_skew
  exact ⟨μ, 𝓕, hμ, inferInstance, hF, h1⟩

end GlobalTheory.SkewVol
