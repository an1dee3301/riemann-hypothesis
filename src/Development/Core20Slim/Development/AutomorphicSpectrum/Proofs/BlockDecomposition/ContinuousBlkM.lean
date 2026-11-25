module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open scoped ComplexConjugate

def blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks b (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) (star u))
      (Matrix.of fun _ _ => (d : ℂ)))

theorem blkM_mem {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) :
    blkM (b : Matrix (Fin n) (Fin n) ℂ) u d ∈ hermC (n + 1) := by
  have hb : (b : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b.2
  rw [mem_hermC]
  unfold blkM
  simp only [Matrix.reindex_apply]
  apply Matrix.IsHermitian.submatrix
  apply Matrix.IsHermitian.fromBlocks hb
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · ext i j
    simp [Matrix.conjTranspose_apply]

def blk {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) : hermC (n + 1) :=
  ⟨blkM (b : Matrix (Fin n) (Fin n) ℂ) u d, blkM_mem b u d⟩

theorem continuous_blkM {n : ℕ} :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) × ℝ => blkM x.1 x.2.1 x.2.2) := by
  refine continuous_matrix fun i j => ?_
  unfold blkM
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.star_apply,
      Matrix.of_apply]
  all_goals fun_prop

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
