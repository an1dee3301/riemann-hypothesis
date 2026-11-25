module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Operations

@[expose] public section

open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  first | exact @GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | exact GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | (intros; apply GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair <;> assumption)
