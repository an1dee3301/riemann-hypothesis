module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisati
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
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
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem g_ext {n : ℕ} {g h : G D n} (e : mat g = mat h) : g = h := by
  unfold mat at e
  exact Subtype.ext (Units.ext e)

theorem exists_slice {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (x0 : Mx D m n)
    (z : Matrix (Fin m) (Fin n) ℂ) : ∃ x : Mx D m n, compAt θ τ x = z ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x0) ∧ x.map (finPart D) = x0.map (finPart D) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.AdForm.RatMove.realPt_spec hθ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0)
  refine ⟨x0 + GlobalTheory.AdForm.realPt θ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0), ?_, ?_, ?_⟩
  · rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp
  · intro τ' h
    rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp [h]
  · rw [Matrix.map_add _ (map_add (finPart D)), h1, add_zero]

theorem tens_at {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) (x : Mx D m n) (u : Matrix (Fin m) (Fin n) ℂ)
    (hx : compAt θ τ x = fr * u) : tens θ τ fr f Ψ x = f u * Ψ x := by
  simp only [tens, hx, Matrix.nonsing_inv_mul_cancel_left _ _ hfr]

theorem awayCls_zero {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    AwayCls θ τ fr (0 : Mx D m n → ℂ) := by
  refine ⟨fun _ _ _ _ => rfl, fun f _ => ?_⟩
  have : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
    funext x
    simp [tens]
  rw [this]
  exact zero_mem _

theorem exists_nU (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : ∃ y : GR n, mR y = nU b := by
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨nU b, nU (-b), by simp [nU, Matrix.fromBlocks_multiply], by simp [nU, Matrix.fromBlocks_multiply]⟩
  have hu : u ∈ GR n := by
    show InG (nU b)
    simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
    simp
  exact ⟨⟨u, hu⟩, rfl⟩

theorem component_block_matrix (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem finite_part_block_matrix {n : ℕ} (a b c d : Mx D n n) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem neg_block_matrix {R : Type} [CommRing R] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_neg]
  rfl

theorem jsq {R : Type} [CommRing R] {n : ℕ} :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  rw [GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, ← GlobalTheory.StdUnn.Frame.block_matrix_one, neg_block_matrix]
  simp

theorem mat_inv_w {n : ℕ} (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat w⁻¹ = -blk4 0 1 (-1) 0 := by
  have h1 : mat w⁻¹ * mat w = 1 := by
    show mat (w⁻¹ * w) = 1
    rw [inv_mul_cancel]
    rfl
  have h2 : mat w * (-mat w) = 1 := by rw [mul_neg, hw, jsq, neg_neg]
  calc mat w⁻¹ = mat w⁻¹ * (mat w * (-mat w)) := by rw [h2, mul_one]
    _ = -mat w := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [hw]

end PositivityTheory.Rg.Sw.Glob.OG
