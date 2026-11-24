module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealLatticeLineCoefficients
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_lattice_line_coefficients : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  first | exact @GlobalTheory.latticeLine_fractionalIdeal | exact GlobalTheory.latticeLine_fractionalIdeal | (intros; apply GlobalTheory.latticeLine_fractionalIdeal <;> assumption)
