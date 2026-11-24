module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebra
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Init.Prelude
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet <;> assumption)
