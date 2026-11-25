module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoE
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoF
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFiniteStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoD
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  delta PositivityTheory.Rg.Sw.Glob.phiS
  rw [dite_eq_left h]

theorem tens_add_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (a : ℂ)
    (f g : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) :
    tens θ τ fr (a • f + g) Ψ = a • tens θ τ fr f Ψ + tens θ τ fr g Ψ := by
  funext x
  delta PositivityTheory.Rg.Sw.Glob.tens
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (a * f (fr⁻¹ * compAt θ τ x) + g (fr⁻¹ * compAt θ τ x)) * Ψ x = _
  ring

theorem tensor_gaussian_vacuum_injective {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr g (psi0 θ V n l s τ)) : f = g := by
  have hdet : IsUnit fr.det := hfr.1
  suffices hU : ∀ U : Matrix (Fin V.rank) (Fin n) ℂ, f U = g U from funext hU
  intro U
  have hx := congrFun h (xL θ τ (fr * U))
  have hc : compAt θ τ (xL θ τ (fr * U)) = fr * U := by
    have h1 := congrFun (compAt_xL hθ τ (fr * U)) τ
    simpa [dirAt_self] using h1
  have hp : psi0 θ V n l s τ (xL θ τ (fr * U)) = 1 := by
    show gAway V l s τ (fun τ' => compAt θ τ' (xL θ τ (fr * U))) *
      g0 D V.rank n (fun i j => finPart D (xL θ τ (fr * U) i j)) = 1
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ, gaussian_at_zero_eq_one, one_mul]
  have hinv : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hdet, Matrix.one_mul]
  change f (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) =
    g (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) at hx
  rw [hc, hp, hinv, mul_one, mul_one] at hx
  exact hx

end PositivityTheory.Rg.Sw.Glob.RhoH
