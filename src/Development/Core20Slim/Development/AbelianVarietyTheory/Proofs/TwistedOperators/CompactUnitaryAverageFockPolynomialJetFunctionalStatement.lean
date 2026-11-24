module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryAverageFockPolynomialJetFunctional
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  first | exact @GlobalTheory.AvgJet.avg_jet | exact GlobalTheory.AvgJet.avg_jet | (intros; apply GlobalTheory.AvgJet.avg_jet <;> assumption)
