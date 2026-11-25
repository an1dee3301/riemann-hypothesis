module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
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
theorem _root_.GlobalTheory.T.zetaIdentity_transport_localFieldIso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [MeasurableSpace k'] [BorelSpace k'] (j : k ≃+* k'), IsLocIso j → ∀ (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C] (σ : Fin a ⊕ A' ≃ C)
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k')) [μ'.IsHaarMeasure] (ϖ : kˣ) (ϖ' : k'ˣ), IsUnif ϖ → IsUnif ϖ' →
    ∀ (ν β : kˣ →* ℂˣ) (ν' β' : k'ˣ →* ℂˣ), (∀ x, ν x = ν' (Units.map (j : k →* k') x)) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a) C k' → ℂ) (Ψ : Matrix A' C k' → ℂ),
      bigP (haarVol (KO k' (Fin a))) ϖ' σ ν' β' Ξ = smallP μ' σ ν' (ν' * β') Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (X.map j)) = smallP μ σ ν (ν * β) fun Y => lam * Ψ (Y.map j) := by
  first | exact @GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | exact GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | (intros; apply GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport <;> assumption)
