module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.IndefiniteUnitaryLieOrthonormalBasesProps
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_unitary_lie_orthonormal_bases_props : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε ∧ (kB ε i)ᴴ = -kB ε i ∧ hs (kB ε i) ≤ 1) ∧ ∀ b, pB ε b ∈ lieSet ε ∧ (pB ε b)ᴴ = pB ε b := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lie | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lie | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lie <;> assumption)
