module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignaturePosSmulBlockDiagonalReindex
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHermitianSignature_pos_smul_blockDiagonalReindexed : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA : Matrix (Fin a) (Fin a) ℂ) (GB : Matrix (Fin b) (Fin b) ℂ) {pa qa pb qb : ℕ} {κ : ℝ},
    0 < κ → Formalism.UG.HasSignature GA pa qa → Formalism.UG.HasSignature GB pb qb →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) (pa + pb) (qa + qb) := by
  first | exact @GlobalTheory.SigBlockSum.hasSig_smul_blk | exact GlobalTheory.SigBlockSum.hasSig_smul_blk | (intros; apply GlobalTheory.SigBlockSum.hasSig_smul_blk <;> assumption)
