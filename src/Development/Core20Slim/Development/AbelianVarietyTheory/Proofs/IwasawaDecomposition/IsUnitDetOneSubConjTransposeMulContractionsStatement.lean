module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions : ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → IsUnit (1 - Aᴴ * B).det := by
  first | exact @GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | exact GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | (intros; apply GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions <;> assumption)
