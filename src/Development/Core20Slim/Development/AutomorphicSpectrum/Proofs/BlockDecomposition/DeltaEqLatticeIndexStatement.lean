module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_eq_lattice_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Matrix (Fin m) (Fin m) K), delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index <;> assumption)
