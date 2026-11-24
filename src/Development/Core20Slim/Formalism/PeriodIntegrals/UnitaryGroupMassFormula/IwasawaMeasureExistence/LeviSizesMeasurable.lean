module

public import Formalism.PeriodIntegrals.LatCountG
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.EnergyIdentity
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
public import Development.Core20Slim.Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DetNorm
public import Formalism.HermitianLattices.StatementMass
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.Nrm

open Matrix NumberField Topology Filter MeasureTheory Formalism.MainNotions.S
  Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.GLOne
open scoped TensorProduct nonZeroDivisors

section Top

variable (I : AutInst)

attribute [local instance] AfT.tAf

theorem topRing : IsTopologicalRing (AEf I) := AfT.isTopologicalRing_tAf I

theorem t2 : T2Space (AEf I) := AfT.t2Space_finite_adeles_ext I

attribute [local instance] topRing t2

def mAf : MeasurableSpace (AEf I) := borel (AEf I)

attribute [local instance] mAf

theorem borel_mAf : BorelSpace (AEf I) := ⟨rfl⟩

attribute [local instance] borel_mAf






end Top

attribute [local instance] AfT.tAf topRing t2 mAf borel_mAf

end PI.IwaMeasEx.Nrm

end
