module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ramifiedChar_det_singularMatrixCoset_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (μ : Measure (GL A' k)) [μ.IsMulLeftInvariant] (ν : kˣ →* ℂˣ) (z : ℂ), ¬ IsUnram ν → ∀ (c : kˣ) (x : Matrix A' A' k), x.det = 0 → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  first | exact @GlobalTheory.CosetVanish.integral_coset_singular_eq_zero | exact GlobalTheory.CosetVanish.integral_coset_singular_eq_zero | (intros; apply GlobalTheory.CosetVanish.integral_coset_singular_eq_zero <;> assumption)
