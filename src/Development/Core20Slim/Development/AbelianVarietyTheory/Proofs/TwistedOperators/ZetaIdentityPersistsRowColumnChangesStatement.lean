module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIdentity_persists_row_column_changes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a a₁ : ℕ) (ha : a = a₁) (A' : Type) [Fintype A'] [DecidableEq A'] (A₁ : Type) [Fintype A₁] [DecidableEq A₁] (C : Type) [Fintype C] [DecidableEq C] (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eB : A' ≃ A₁) (eC : C ≃ C₁)
    (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a₁ ⊕ A₁ ≃ C₁) (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ₁ : Measure (GL A₁ k)) [μ₁.IsHaarMeasure]
    (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a₁) C₁ k → ℂ) (Ψ : Matrix A₁ C₁ k → ℂ),
      bigP (haarVol (KO k (Fin a₁))) ϖ σ₁ ν β Ξ = smallP μ₁ σ₁ ν (ν * β) Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (finCongr ha) eC (gA.val * X * (invT c).val))) =
        smallP μ σ ν (ν * β) fun Y => lam * Ψ (reindex eB eC (gB.val * Y * c.val)) := by
  first | exact @GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change | exact GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change | (intros; apply GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change <;> assumption)
