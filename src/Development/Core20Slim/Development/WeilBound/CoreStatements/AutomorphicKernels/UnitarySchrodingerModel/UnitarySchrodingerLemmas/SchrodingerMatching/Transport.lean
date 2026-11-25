module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

section Transport

variable {D : D7} {n : ℕ}

def hermToME : hermA D n ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n where
  toFun := hermTo
  invFun := hermFrom
  left_inv := hermFrom_hermTo
  right_inv := hermTo_hermFrom
  measurable_toFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermTo.measurable
  measurable_invFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermFrom.measurable

theorem integral_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) :
    ∫ b, W b ∂(lam.map hermTo) = ∫ b, W (hermTo b) ∂lam :=
  (hermToME (D := D) (n := n)).measurableEmbedding.integral_map W

theorem integrable_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) (h : Integrable (fun b => W (hermTo b)) lam) :
    Integrable W (lam.map hermTo) :=
  ((hermToME (D := D) (n := n)).measurableEmbedding.integrable_map_iff).2 h

end Transport

end PositivityTheory.PfSWUS.SwMatch

end
