module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Formalism.IndefR.Datum

namespace PositivityTheory.Rg.Sw.Glob

theorem exists_unitary_diag {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ} (hT : T.IsHermitian) :
    ∃ (W : Matrix (Fin k) (Fin k) ℂ) (lam : Fin k → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      Wᴴ * T * W = diagonal (fun i => (lam i : ℂ)) := by
  refine ⟨(hT.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ), hT.eigenvalues, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have := hT.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this

theorem exists_normal {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M.PosDef) : ∃ C : Matrix (Fin k) (Fin k) ℂ,
    Cᴴ * M * C = 1 := by
  have hpos := hM.eigenvalues_pos
  have hUU : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hd : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * M * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) =
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
    have := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this
  generalize (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = U at hUU hd
  generalize hM.1.eigenvalues = μ at hpos hd
  refine ⟨U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)), ?_⟩
  have hCd : (diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))ᴴ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, hCd]
  calc diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * Uᴴ * M * (U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))
      = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * (Uᴴ * M * U) * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        have hp := hpos i
        have hs : (Real.sqrt (μ i)) ^ 2 = μ i := Real.sq_sqrt hp.le
        have hs0 : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
        have hc : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
        field_simp
        rw [← Complex.ofReal_pow, hs]

theorem frame_of_cartan {k : ℕ} (G S : Matrix (Fin k) (Fin k) ℂ) (h : IsCartanInv G S) :
    ∃ (ε : Fin k → Bool) (fr : Matrix (Fin k) (Fin k) ℂ), IsUnit fr.det ∧ frᴴ * G * fr = diagonal (sgn ε) ∧
      frᴴ * (G * S) * fr = 1 := by
  obtain ⟨hSS, hSG, hM⟩ := h
  have hMh : (G * S)ᴴ = G * S := hM.1
  have hGh : Gᴴ = G := by
    have h1 : Sᴴ * Sᴴ = 1 := by rw [← conjTranspose_mul, hSS, conjTranspose_one]
    have h2 : Sᴴ * Gᴴ = G * S := by rw [← conjTranspose_mul]; exact hMh
    calc Gᴴ = Sᴴ * Sᴴ * Gᴴ := by rw [h1, Matrix.one_mul]
      _ = Sᴴ * (Sᴴ * Gᴴ) := by rw [Matrix.mul_assoc]
      _ = Sᴴ * (G * S) := by rw [h2]
      _ = Sᴴ * G * S := by rw [Matrix.mul_assoc]
      _ = G := hSG
  obtain ⟨C, hCMC⟩ := exists_normal hM
  have hCCM : C * (Cᴴ * (G * S)) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin k))).mp hCMC
  have hTh : (Cᴴ * G * C).IsHermitian := by
    show (Cᴴ * G * C)ᴴ = Cᴴ * G * C
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, Matrix.mul_assoc]
  have hTT : (Cᴴ * G * C) * (Cᴴ * G * C) = 1 := by
    have e1 : C * Cᴴ * G = S := by
      have : G = G * S * S := by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      calc C * Cᴴ * G = C * (Cᴴ * (G * S)) * S := by
            conv_lhs => rw [this]
            simp only [Matrix.mul_assoc]
        _ = S := by rw [hCCM, Matrix.one_mul]
    calc (Cᴴ * G * C) * (Cᴴ * G * C) = Cᴴ * G * (C * Cᴴ * G) * C := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (G * S) * C := by rw [e1]; simp only [Matrix.mul_assoc]
      _ = 1 := hCMC
  obtain ⟨W, lam, hWW, hWW', hTd⟩ := exists_unitary_diag hTh
  have hsq : ∀ i, lam i = 1 ∨ lam i = -1 := by
    have hD : diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ)) = 1 := by
      rw [← hTd]
      calc Wᴴ * (Cᴴ * G * C) * W * (Wᴴ * (Cᴴ * G * C) * W)
          = Wᴴ * (Cᴴ * G * C) * (W * Wᴴ) * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hWW', Matrix.mul_one, Matrix.mul_assoc Wᴴ (Cᴴ * G * C) (Cᴴ * G * C), hTT, Matrix.mul_one, hWW]
    intro i
    have := congrFun (congrFun hD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at this
    have h2 : (lam i) * (lam i) = 1 := by exact_mod_cast this
    have h3 : (lam i - 1) * (lam i + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h3 with h | h
    · left; linarith
    · right; linarith
  refine ⟨fun i => decide (lam i = 1), C * W, ?_, ?_, ?_⟩
  · have hinv : ((C * W)ᴴ * (G * S)) * (C * W) = 1 := by
      rw [conjTranspose_mul]
      calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]
    exact isUnit_det_of_left_inverse hinv
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * G * (C * W) = Wᴴ * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (lam i : ℂ)) := hTd
      _ = diagonal (sgn fun i => decide (lam i = 1)) := by
          congr 1; funext i
          simp only [sgn]
          rcases hsq i with h | h
          · simp [h]
          · simp [h] <;> norm_num
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]

theorem sFrame : SFrame := by
  intro D V τ s h
  exact frame_of_cartan _ _ h

end PositivityTheory.Rg.Sw.Glob
