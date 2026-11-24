module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFamilyExpandCreationAnnihilation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_family_expand_creation_annihilation : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    ∀ c : W → Matrix (Ix P Q) (Ix R S) ℂ, H c = ∑ j : W × (Ix P Q × Ix R S),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockD H j) := by
  first | exact @GlobalTheory.CCRFock.heis_expand | exact GlobalTheory.CCRFock.heis_expand | (intros; apply GlobalTheory.CCRFock.heis_expand <;> assumption)
