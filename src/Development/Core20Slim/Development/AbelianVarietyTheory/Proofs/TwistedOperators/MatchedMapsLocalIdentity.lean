module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThK.PolMatchStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_lin_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (T : Module.End ℂ ((κ → AF F) → ℂ)) {φ ψ φ₁ ψ₁ χ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (hψ : ψ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T ψ ψ₁) (a b : ℂ) (h₃ : Acts (evFin F v) T (a • φ + b • ψ) χ) :
    χ = a • φ₁ + b • ψ₁ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hs : a • φ + b • ψ ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem a hφ) ((SB _).smul_mem b hψ)
  have hlin : ∀ x y : (κ → Fv F v) → ℂ,
      tens (evFin F v) (a • x + b • y) R = a • tens (evFin F v) x R + b • tens (evFin F v) y R := by
    intro x y; funext z; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  refine GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ hs).1 ?_
  rw [← h₃ R (hR _ hs), hlin, map_add (f := _), map_smul, map_smul, h₁ R (hR _ hφ), h₂ R (hR _ hψ), hlin]

open Classical in
theorem pure_update (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f : SInf F κ)
    (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (κ → Fv F w))
    (hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ₁ : (κ → Fv F v) → ℂ} (hA : Acts (evFin F v) T (φ v) φ₁) :
    T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = tens (evFin F v) (φ v) r := by rw [hrt, Function.update_eq_self]
  have hRest : Rest (evFin F v) (φ v) r := ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  rw [e1, hA r hRest, hrt]

end Local

end GlobalTheory.ThK.PolMatchStep

end
