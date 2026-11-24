module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Jab.WsInteg

variable {D : D7}

def hermE (D : D7) (r : ℕ) (b : hermA D r) : HermR (AF D.host.F) D.sp.cm.sig r :=
  ⟨b.1, fun i j => by
    have h := congrFun (congrFun b.2 i) j
    simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h⟩

theorem integrable_of_addEquiv {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V']
    (g : V → V') (k : V' → V) (h1 : Function.LeftInverse k g) (h2 : Function.RightInverse k g)
    (hadd : ∀ x y, g (x + y) = g x + g y) (hc : Continuous g) (hc' : Continuous k)
    (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (ν : Measure V') (hν : ν.IsAddHaarMeasure)
    (f : V' → ℂ) (hf : Integrable (fun b => f (g b)) μ) : Integrable f ν := by
  let e : V ≃+ V' := { toFun := g, invFun := k, left_inv := h1, right_inv := h2, map_add' := hadd }
  let h : V ≃ₜ V' := { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hc hc'
  have hi : Integrable f (μ.map e) := (integrable_map_equiv h.toMeasurableEquiv f).2 hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (μ.map e)]
  exact hi.smul_measure_nnreal


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_of_hermE {r : ℕ} (lam : Measure (hermA D r)) (hlam : lam.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (f : HermR (AF D.host.F) D.sp.cm.sig r → ℂ) (hf : Integrable (fun b => f (hermE D r b)) lam) :
    Integrable f db := by
  haveI : IsTopologicalAddGroup (Mx D r r) := inferInstanceAs (IsTopologicalAddGroup (Fin r → Fin r → AE D))
  haveI i3 : SecondCountableTopology (Mx D r r) := inferInstanceAs (SecondCountableTopology (Fin r → Fin r → AE D))
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  haveI : SecondCountableTopology (HermR (AF D.host.F) D.sp.cm.sig r) :=
    @Topology.IsInducing.secondCountableTopology _ _ _ _ _ i3 Topology.IsInducing.subtypeVal
  exact integrable_of_addEquiv (hermE D r) (fun S => ⟨S.1, Matrix.ext fun a c => S.2 a c⟩) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (continuous_subtype_val.subtype_mk _) (continuous_subtype_val.subtype_mk _)
    lam hlam db hdb f hf

end PositivityTheory.PfWsf.Jab.WsInteg
