module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise

namespace GlobalTheory

theorem ideal_map_smul_isLattice (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) :
    I ≠ ⊥ → Submodule.IsLattice E L →
      Submodule.IsLattice E (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  intro hI hL
  have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) • L ≤ L := Submodule.smul_le_right
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hdE : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hd0
    have h1 : algebraMap (𝓞 F) (𝓞 E) d = 0 := by exact_mod_cast h
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h1)
  set u : Eˣ := Units.mk0 _ hdE
  have hsub : (u • L : Submodule (𝓞 E) (Fin n → E)) ≤ I.map (algebraMap (𝓞 F) (𝓞 E)) • L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have : (u • y : Fin n → E) = (algebraMap (𝓞 F) (𝓞 E) d) • y := by
      rw [Units.smul_def, Units.val_mk0, ← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) d) y]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hdI) hy
  exact Submodule.IsLattice.of_fg E (Submodule.FG.of_le hL.fg hle)

end GlobalTheory
