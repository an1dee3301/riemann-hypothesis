module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameTestFunction_transpose_integralGL_mul_eq_char : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (u : GL A k), u ∈ KO k A → ∀ h : GL D k,
      (ν (gdet u) : ℂ) * fFun μ σ ν Ψ (u.valᵀ * (X0 k σ * (invT h).val)) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  first | exact @GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO | exact GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO | (intros; apply GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO <;> assumption)
