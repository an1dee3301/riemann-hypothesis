module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

namespace GlobalTheory.HeisLatVac

theorem vacFn_hasCompactSupport_of_isCompact : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)))
    (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    IsCompact (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) → HasCompactSupport (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  intro F _ _ v κ _ ψ₀ Λ χ x₀ hΛ
  have hK : IsCompact ((fun u : (κ → Fv F v) × (κ → Fv F v) => x₀ + u.1) '' (Λ : Set _)) :=
    hΛ.image (continuous_const.add continuous_fst)
  refine HasCompactSupport.intro hK ?_
  intro x hx
  unfold vacFn
  rw [dite_eq_right]
  rintro ⟨u, hu, rfl⟩
  exact hx ⟨u, hu, rfl⟩

end GlobalTheory.HeisLatVac
