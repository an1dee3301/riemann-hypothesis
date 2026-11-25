module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransport
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  first | exact @GlobalTheory.fromBlocks_unitary_transfer | exact GlobalTheory.fromBlocks_unitary_transfer | (intros; apply GlobalTheory.fromBlocks_unitary_transfer <;> assumption)
