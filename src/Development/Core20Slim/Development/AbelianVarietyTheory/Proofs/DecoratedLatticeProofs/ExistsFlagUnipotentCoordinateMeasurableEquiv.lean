module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinatesStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf

def coordFlip (D : D7) (ρ m : ℕ) : skewA D ρ × (Mx D ρ m × UX D ρ) ≃ₜ UX D ρ × (Mx D ρ m × skewA D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ m) := (lattice_Mx D ρ m).1
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  { toFun := fun p => (p.2.2⁻¹, (-p.2.1, -p.1))
    invFun := fun q => (-q.2.2, (-q.2.1, q.1⁻¹))
    left_inv := fun p => Prod.ext (neg_neg _) (Prod.ext (neg_neg _) (inv_inv _))
    right_inv := fun q => Prod.ext (inv_inv _) (Prod.ext (neg_neg _) (neg_neg _))
    continuous_toFun := continuous_snd.snd.inv.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.neg)
    continuous_invFun := continuous_snd.snd.neg.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.inv) }

theorem coordFlip_apply (D : D7) (ρ m : ℕ) (p : skewA D ρ × (Mx D ρ m × UX D ρ)) :
    coordFlip D ρ m p = (p.2.2⁻¹, (-p.2.1, -p.1)) := rfl

end GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem flagCoord_measEquiv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ),
    ∃ e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d,
      ∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1) := by
  intro D V V₀ ρ d
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_homeomorph_wittFlagCoordinates D V V₀ ρ d
  haveI : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  haveI : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  haveI : SecondCountableTopology (UX D ρ) := (GlobalTheory.UnitU.topology D ρ).2.1
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  refine ⟨((coordFlip D ρ V₀.rank).trans (Φ.trans (Homeomorph.inv (flagN d)))).toMeasurableEquiv, fun p => ?_⟩
  change (((Φ (coordFlip D ρ V₀.rank p))⁻¹ : flagN d) : GA D V) = _
  rw [Subgroup.coe_inv, hΦ, coordFlip_apply]
  change (d.levi ((p.2.2⁻¹ : UX D ρ) : GL (Fin ρ) (AE D)) * (d.nB (-p.2.1) * d.nC (-p.1)))⁻¹ = _
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, d.nB_inv, d.nC_inv, neg_neg, neg_neg, Subgroup.coe_inv, map_inv, inv_inv,
    mul_assoc]

end GlobalTheory.Unf

end
