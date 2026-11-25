module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHermitianSignature
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Prelude
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_hermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  first | exact @GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | exact GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | (intros; apply GlobalTheory.PlaneSkew.CartanInv.exists_isCartan <;> assumption)
