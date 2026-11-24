module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.FinFockLin

theorem finF_lin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X),
  IsFinF ψ θ ε A B 0 ∧ (∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g)) ∧
  (∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f)) ∧
  (∀ f g P, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g →
    fockF ψ θ ε A B (f + g) P = fockF ψ θ ε A B f P + fockF ψ θ ε A B g P) ∧
  ∀ (c : ℂ) f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B (c • f) P = c • fockF ψ θ ε A B f P := by
  intro D ψ θ hψ hθ ε M X A B
  have hsm : ∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f) := by
    intro c f hf
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c hf.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z c hf.1, hf.2 τ z, smul_zero]
  have hadd : ∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g) := by
    intro f g hf hg
    refine ⟨GlobalTheory.OrientedHeis.theta_add hf.1 hg.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_add hψ hθ τ _ z hf.1 hg.1, hf.2 τ z, hg.2 τ z, add_zero]
  have h0 : IsFinF ψ θ ε A B 0 := by
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, fun τ z => ?_⟩
    have h := GlobalTheory.FockIndep.annih_smul hψ hθ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) z 0
      (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε M) (T := X))
    simpa only [zero_smul] using h
  refine ⟨h0, hadd, hsm, fun f g P hf hg => ?_, fun c f P hf => ?_⟩
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb 1 hf.1 hg.1 P
    rw [one_smul, one_smul] at h
    exact h
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb c hf.1
      h0.1 P
    rw [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ _ _ hψ hθ, add_zero] at h
    exact h

end GlobalTheory.FinFockLin

end
