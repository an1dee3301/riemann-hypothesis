module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
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
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesUnimod

theorem besGrp_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
    (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ A L ρ d o μ hμ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨ν, 𝓝, hν⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  obtain ⟨hνH, h𝓝, h𝓝1⟩ := hν
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  let μA : Measure (GA D A) := Measure.haar
  have hHaar := ((GlobalTheory.MixPer.jacGrp_besGrp_haar D V V₀ A L ρ d o ν 𝓝 ⟨hνH, h𝓝, h𝓝1⟩).2.2 μA inferInstance)
  haveI : LocallyCompactSpace (flagN d) := hNc.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  haveI : Countable (NFlagQ V d.e) := hinj.countable
  haveI : ν.IsMulRightInvariant :=
    GlobalTheory.SemiHaar.rightInv_of_fd (NFlagQ V d.e) ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  haveI : μA.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A μA inferInstance
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d n hn (o.emb (h, 1))
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) (embA d o) hNc hcA hnA μA ν
  haveI : LocallyCompactSpace (besGrp d o) := by
    obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) (embA d o) hnA hcA (GlobalTheory.BesProj.exists_continuous_proj D V V₀ A L ρ d o)
    exact e.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (besGrp d o) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨κ, k1, k2⟩ : ∃ κ : Measure (besGrp d o), κ.IsHaarMeasure ∧ κ.IsMulRightInvariant := ⟨_, hHaar, hR⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ κ]
  infer_instance

end GlobalTheory.BesUnimod
