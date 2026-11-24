module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapMulMtEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarCoords
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
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
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagModulus

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem wittHyperbolic_conj_smallerGroup_coords (d : HypDec S S₀ ρ) (h : GA D S₀) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank)
    (c : skewA D ρ) : d.emb0 h * (d.levi u * (d.nB b * d.nC c)) * (d.emb0 h)⁻¹ =
      d.levi u * (d.nB (b ⬝ mt S₀ h⁻¹) * d.nC c) := by
  simp only [mul_assoc]
  rw [← mul_assoc (d.emb0 h) (d.levi u), d.wittHyperbolic_anisotropic_commute_levi h u, mul_assoc, ← mul_assoc (d.emb0 h) (d.nB b),
    d.wittHyperbolic_anisotropic_conj_nB b h, mul_assoc, ← mul_assoc (d.emb0 h) (d.nC c), d.wittHyperbolic_anisotropic_commute_nC c h, mul_assoc, mul_inv_cancel,
    mul_one]

theorem map_conj_smallerUnitary_flagUnipotent_haar : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (ν : Measure (flagN d)),
    ν.IsHaarMeasure → ∀ h : GA D S₀,
      ν.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν.map Subtype.val := by
  intro D S S₀ ρ d ν hν h
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  obtain ⟨hlc, hsc, -, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  obtain ⟨μ, lB, lC, hμ, hB, hC, sμ, sB, sC, hΦ, ν₀, hν₀, hmap⟩ := GlobalTheory.HaarCoords.haar_coords D S S₀ ρ d
  have hk : ν = Measure.haarScalarFactor ν ν₀ • ν₀ := Measure.isMulLeftInvariant_eq_smul ν ν₀
  have hconj : Measurable (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hval : Measurable (Subtype.val : flagN d → GA D S) := measurable_subtype_coe
  have hf : Measurable (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hT : Measurable (Prod.map (id : UX D ρ → UX D ρ)
      (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ))) :=
    measurable_id.prodMap (hf.prodMap measurable_id)
  have key : ν₀.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν₀.map Subtype.val := by
    have e1 : (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) =
        (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘ Subtype.val := rfl
    rw [e1, ← Measure.map_map hconj hval, hmap, Measure.map_map hconj hΦ]
    have e2 : (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∘
          Prod.map (id : UX D ρ → UX D ρ)
            (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ)) :=
      funext fun p => wittHyperbolic_conj_smallerGroup_coords d h p.1.1 p.2.1 p.2.2
    rw [e2, ← Measure.map_map hΦ hT]
    congr 1
    rw [← Measure.map_prod_map _ _ measurable_id (hf.prodMap measurable_id), ← Measure.map_prod_map _ _ hf measurable_id,
      Measure.map_id, Measure.map_id, GlobalTheory.AdelicModulus.RowMat.map_mul_mt_eq D S₀ ρ lB hB h⁻¹]
  rw [hk, Measure.map_smul, Measure.map_smul, key]
  · exact hval.aemeasurable
  · exact (hconj.comp hval).aemeasurable

end GlobalTheory.FlagModulus

end
