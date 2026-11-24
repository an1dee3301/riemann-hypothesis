module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutUnitaryPointStabilizesLattices
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentCut_unitaryPoint_stabilizes_lattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₁ ⊆ S →
      (∀ w ∉ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u * e = 0 ∨ u * e = u) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  first | exact @GlobalTheory.IdemCut.idempotentCut_latticeStabilizer | exact GlobalTheory.IdemCut.idempotentCut_latticeStabilizer | (intros; apply GlobalTheory.IdemCut.idempotentCut_latticeStabilizer <;> assumption)
