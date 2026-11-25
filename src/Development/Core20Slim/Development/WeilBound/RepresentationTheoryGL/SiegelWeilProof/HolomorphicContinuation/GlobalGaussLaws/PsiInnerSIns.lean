module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousInsT
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiEqOfFin
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem map_inner (V : HSp D) (τ : D.what₂.Tau) (x y : Mx D V.rank n) :
    (inner V x y).map (psiT D τ) = (x.map (psiT D τ))ᴴ * (gramAt D V τ * y.map (psiT D τ)) := by
  have h1 : (adj x).map (psiT D τ) = (x.map (psiT D τ))ᴴ := by
    ext i j
    simp only [adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact psiT_sigR D τ (x j i)
  have h2 : (gA V).map (psiT D τ) = gramAt D V τ := by
    ext i j
    simp only [gA, rat, Matrix.map_apply, gramAt]
    exact psiT_inclR D τ _
  show (adj x * (gA V * y)).map (psiT D τ) = _
  rw [Matrix.map_mul, Matrix.map_mul, h1, h2]

set_option synthInstance.maxHeartbeats 400000 in
theorem psiT_trace {a : ℕ} (τ : D.what₂.Tau) (M : Matrix (Fin a) (Fin a) (AE D)) :
    psiT D τ (Matrix.trace M) = Matrix.trace (M.map (psiT D τ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

set_option synthInstance.maxHeartbeats 400000 in
theorem finPart_trace {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D)) :
    finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

set_option synthInstance.maxHeartbeats 400000 in
theorem finMap_inner (V : HSp D) (x y : Mx D V.rank n) (hy : y.map (finPart D) = 0) :
    (inner V x y).map (finPart D) = 0 := by
  show (adj x * (gA V * y)).map (finPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, hy, Matrix.mul_zero, Matrix.mul_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_inner_sIns {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (x : Mx D V.rank n) (u : Fin V.rank → Fin n → ℂ) :
    ψ (trA (Matrix.trace (inner V x (sIns τ fr u)))) =
      Complex.exp (Complex.I * ((2 * tLoc l τ : ℝ) : ℂ) *
        (((Matrix.of (piF θ τ fr x))ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ)) := by
  have hins : ∀ τ', (sIns (D := D) τ fr u).map (psiT D τ') = if τ' = τ then fr * Matrix.of u else 0 := by
    intro τ'
    have := compAt_insT (D := D) hθ τ τ' (fr * Matrix.of u)
    rw [eq_thetaC D hθ] at this
    exact this
  rw [psi_trA_tau hθ hl τ]
  · congr 2
    · simp only [tLoc]; push_cast; ring
    · rw [psiT_trace, map_inner, hins, if_pos rfl]
      congr 2
      obtain ⟨hdet, hg, -⟩ := hfr
      have hx : Matrix.of (piF θ τ fr x) = fr⁻¹ * x.map (psiT D τ) := by
        rw [eq_thetaC D hθ] ; rfl
      rw [hx, ← hg, Matrix.conjTranspose_mul]
      have hinv : (fr⁻¹)ᴴ * frᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (fr⁻¹)ᴴ frᴴ, hinv, Matrix.one_mul]
  · intro τ' hne
    rw [psiT_trace, map_inner, hins, if_neg hne, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero]
  · rw [finPart_trace, finMap_inner V x (sIns τ fr u) (finMap_insT τ (fr * Matrix.of u)), Matrix.trace_zero]

end PositivityTheory.Rg.Sw.Glob.FTP
