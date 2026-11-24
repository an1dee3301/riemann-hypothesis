module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealQuotientMinorEqConstSmulComplementMinor
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realQuotient_minor_eq_const_smul_complementMinor : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n₀ : D.what₂.Tau → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : PolF D d a →ₗ[ℂ] Pr) (q' : PolF D d a' →ₗ[ℂ] Pr) (σ : (D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr),
    0 < a → 0 < a' → Nontrivial Pr → Function.Surjective q → Function.Surjective q' →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a) ℂ) (P : PolF D d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a') ℂ) (P : PolF D d a'),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) • q' P) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P)) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a' d n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q' P)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D a d n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  first | exact @GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl | exact GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl | (intros; apply GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl <;> assumption)
