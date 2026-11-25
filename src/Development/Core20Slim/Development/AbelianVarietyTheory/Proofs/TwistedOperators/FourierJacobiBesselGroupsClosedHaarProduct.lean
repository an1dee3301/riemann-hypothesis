module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasIsMulLeftInvariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasFiniteOnCompactsAndOpenPos
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapConjSmallerUnitaryFlagUnipotentHaar
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
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
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

theorem jacGrp_besGrp_haar : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ν : Measure (flagN d)) (𝓝 : Set (flagN d)), GlobalTheory.Per.IsUnitN S d.e ν 𝓝 → (IsClosed (jacGrp d : Set (GA D S)) ∧ ∀ μ : Measure (GA D S₀), μ.IsHaarMeasure → (semiMeas (flagN d) d.emb0 μ ν).IsHaarMeasure) ∧ IsClosed (besGrp d o : Set (GA D S)) ∧ ∀ μ : Measure (GA D A), μ.IsHaarMeasure → (semiMeas (flagN d) (embA d o) μ ν).IsHaarMeasure := by
  intro D S S₀ A L ρ d o ν 𝓝 hν
  have hNc : IsClosed (flagN d : Set (GA D S)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag S (isIsoSub_e d)
  have hνH : ν.IsHaarMeasure := hν.1
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn (o.emb (h, 1))
  have hmA : ∀ h, ν.map (fun n : flagN d => embA d o h * n.1 * (embA d o h)⁻¹) = ν.map Subtype.val := fun h =>
    GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH (o.emb (h, 1))
  refine ⟨⟨GlobalTheory.jacGrp_isClosed D S S₀ ρ d, fun μ hμ => ?_⟩, GlobalTheory.BesClosed.besGrp_isClosed D S S₀ A L ρ d o, fun μ hμ => ?_⟩
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }

end GlobalTheory.MixPer

end
