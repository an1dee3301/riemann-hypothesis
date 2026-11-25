module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
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
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
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
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.HaarCoords

theorem transl_nC : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure → lB.IsAddHaarMeasure → lC.IsAddHaarMeasure → SFinite μ → SFinite lB → SFinite lC → ∀ c' : skewA D ρ, ∃ T : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ), MeasurePreserving T (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) ∧ ∀ p, d.levi (T p).1.1 * (d.nB (T p).2.1 * d.nC (T p).2.2) = d.nC c' * (d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d μ lB lC _ _ hC _ _ _ c'
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, -, i3, -⟩ := lattice_Mx D ρ ρ
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : MeasurableAdd₂ (skewA D ρ) := inferInstance
  haveI : MeasurableAdd (skewA D ρ) := inferInstance
  let s : UX D ρ → skewA D ρ := fun u => skewConj (u⁻¹).1.1 c'
  have hinv : Continuous fun u : UX D ρ => (u⁻¹).1.1 := Units.continuous_coe_inv.comp continuous_subtype_val
  have hs : Continuous s := by
    refine Continuous.subtype_mk ?_ _
    exact (hinv.matrix_mul continuous_const).matrix_mul (continuous_adj.comp hinv)
  refine ⟨fun p => (p.1, (p.2.1, s p.1 + p.2.2)), ?_, ?_⟩
  · have hg : Measurable (Function.uncurry fun (u : UX D ρ) (q : Mx D ρ S₀.rank × skewA D ρ) => (q.1, s u + q.2)) :=
      measurable_snd.fst.prodMk ((hs.measurable.comp measurable_fst).add measurable_snd.snd)
    exact (MeasurePreserving.id μ).skew_product hg
      (Filter.Eventually.of_forall fun u => ((MeasurePreserving.id lB).prod (measurePreserving_add_left lC (s u))).map_eq)
  · rintro ⟨u, b, c⟩
    have h := d.levi_mul_nC c' (u⁻¹).1
    have hL : d.levi (u⁻¹).1 = (d.levi u.1)⁻¹ := by rw [Subgroup.coe_inv, map_inv]
    rw [hL] at h
    have h2 : d.nC c' * d.levi u.1 = d.levi u.1 * d.nC (s u) := by
      calc d.nC c' * d.levi u.1 = d.levi u.1 * ((d.levi u.1)⁻¹ * d.nC c') * d.levi u.1 := by rw [mul_inv_cancel_left]
        _ = d.levi u.1 * (d.nC (s u) * (d.levi u.1)⁻¹) * d.levi u.1 := by rw [h]
        _ = d.levi u.1 * d.nC (s u) := by rw [← mul_assoc (d.levi u.1), inv_mul_cancel_right]
    show d.levi u.1 * (d.nB b * d.nC (s u + c)) = d.nC c' * (d.levi u.1 * (d.nB b * d.nC c))
    rw [d.nC_add, ← mul_assoc (d.nC c'), h2, mul_assoc, ← mul_assoc (d.nC (s u)), d.nC_mul_nB, mul_assoc]

end GlobalTheory.HaarCoords
