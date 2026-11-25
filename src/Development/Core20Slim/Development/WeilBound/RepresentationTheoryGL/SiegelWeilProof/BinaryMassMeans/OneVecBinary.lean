module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquidistributionStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMulStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormulaStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocompactnessStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormulaStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfPartsStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvarianceStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExistsStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormulaStatement
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.SingleRowSide.Srside
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfPartsStatement
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace PositivityTheory.Rg.Mass

theorem e1 : E1 :=
  GlobalTheory.T.one_vector_formula_of_parts (GlobalTheory.T.vector_length_formula_of_parts GlobalTheory.T.cocompactness GlobalTheory.T.local_mass_formula) GlobalTheory.T.similitude_invariance GlobalTheory.T.hasse_principle
    (GlobalTheory.T.counting_formula GlobalTheory.T.test_function_exists (GlobalTheory.T.left_side_formula GlobalTheory.T.equidistribution GlobalTheory.T.cocompactness)
      (PositivityTheory.Rg.Mass.LiteralAutomorphy.srside (GlobalTheory.T.mean_value_formula GlobalTheory.T.equidistribution GlobalTheory.T.counting_bound_alt) GlobalTheory.T.local_mass_formula))

theorem oneVecBinary : PositivityTheory.PfSWUS.HMass.OneVecBinary := by
  intro F E _ _ _ _ _ σ hc M J hJ hM hA T hT hd
  subst hM
  exact e1 F E σ hc J hJ (fun x hx => by_contra fun h => hA x h hx) T hT hd

end PositivityTheory.Rg.Mass
