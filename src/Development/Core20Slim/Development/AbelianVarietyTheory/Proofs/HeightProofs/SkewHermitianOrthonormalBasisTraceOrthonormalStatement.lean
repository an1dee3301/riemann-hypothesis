module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length), (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | exact GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal <;> assumption)
