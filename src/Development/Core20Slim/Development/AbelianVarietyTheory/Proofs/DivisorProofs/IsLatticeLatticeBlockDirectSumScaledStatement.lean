module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
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
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_latticeBlockDirectSum_scaled : ∀ {E : Type} [Field E] [NumberField E] {a b d : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E}, 𝔞 ≠ 0 →
    ∀ {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}, Submodule.IsLattice E ΛA →
    Submodule.IsLattice E ΛB → ∀ (e : Fin a ⊕ Fin b ≃ Fin d),
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat 𝔞 ΛA) (GlobalTheory.SkewLat.scLat 𝔞 ΛB) e) := by
  first | exact @GlobalTheory.SkewLat.pairLat_scLat_isLattice | exact GlobalTheory.SkewLat.pairLat_scLat_isLattice | (intros; apply GlobalTheory.SkewLat.pairLat_scLat_isLattice <;> assumption)
