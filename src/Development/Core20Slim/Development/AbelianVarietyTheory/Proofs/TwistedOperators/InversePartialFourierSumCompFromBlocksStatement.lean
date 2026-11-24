module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.InversePartialFourierSumCompFromBlocks
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftResMulSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
        invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  first | exact @GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | exact GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | (intros; apply GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks <;> assumption)
