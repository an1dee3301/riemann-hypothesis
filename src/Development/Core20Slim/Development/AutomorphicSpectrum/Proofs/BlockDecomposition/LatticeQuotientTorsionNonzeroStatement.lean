module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_quotient_torsion_nonzero : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot <;> assumption)
