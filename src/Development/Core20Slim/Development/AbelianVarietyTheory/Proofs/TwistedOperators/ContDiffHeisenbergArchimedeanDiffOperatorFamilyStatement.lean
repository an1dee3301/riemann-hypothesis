module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamily
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Classical
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_heisenbergArchimedeanDiffOperator_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (P p.1) (Q p.1) (G p.1) p.2) := by
  first | exact @GlobalTheory.HeisOrbit.dOp_contDiff_family | exact GlobalTheory.HeisOrbit.dOp_contDiff_family | (intros; apply GlobalTheory.HeisOrbit.dOp_contDiff_family <;> assumption)
