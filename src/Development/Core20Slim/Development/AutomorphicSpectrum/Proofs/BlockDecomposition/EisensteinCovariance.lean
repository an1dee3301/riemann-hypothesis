module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationCovarianceLevi
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceInnerMul
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatImpliesFieldGeneration
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupInductionGenerators
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBruhatDecomposition
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
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
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covar_of (hB : Bruhat) (hR : RatPts) : Covar := by
  intro D n V ψ χ θ μ ω hS γ hγ v Φ Ψ hΨ
  obtain ⟨-, -, -, -, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat hB D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer hR D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem covar : Covar :=
  covar_of GlobalTheory.CompanionTheory.BruhatCell.bruhat GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn

end GlobalTheory.CompanionTheory.EisCovar
