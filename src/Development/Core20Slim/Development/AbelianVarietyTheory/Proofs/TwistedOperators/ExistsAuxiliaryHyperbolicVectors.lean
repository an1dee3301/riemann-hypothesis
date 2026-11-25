module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongrOfSignatureOfAdelicNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StandardGramVectors

open GlobalTheory.FrameComplement 


theorem hasSignature_submatrix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {J : Matrix n n ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature J p q) (e : m ≃ n) :
    Formalism.UG.HasSignature (J.submatrix e e) p q := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  refine hasSignature_of_frame (by rw [Fintype.card_congr e, c]) (Q.submatrix e id) ?_
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id, hQ]







end GlobalTheory.StandardGramVectors
