module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignature
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Prelude
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew.CartanInv

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ :=
  GlobalTheory.CartanEx.exists_isCartan

end GlobalTheory.PlaneSkew.CartanInv
