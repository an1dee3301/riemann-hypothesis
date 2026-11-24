module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.LFun

theorem ideleAt_eq_locIdele_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (x : (Fv F v ⊗[F] E)ˣ) :
    ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) := by
  refine eq_locIdele ?_ ?_
  · exact map_extUnit_zero (fstA F) (inFin v) (inFin_mul v) (fun _ => rfl) x
  · refine FiniteAdeleRing.ext _ fun u => ?_
    rw [finAdEquiv_apply rfl]
    have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
        (finTens F E (ideleAt F E v x : AF F ⊗[F] E)) = (unitFin F E (u.under (𝓞 F)) (ideleAt F E v x) : Fv _ _ ⊗[F] E) := by
      change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) _) = _
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
      rfl
    rw [e]
    by_cases hu : u.under (𝓞 F) = v
    · obtain rfl : u = w := (InertChart.under_eq_iff hw u).1 hu
      subst h
      rw [unitFin_ideleAt_self]
      exact (finSingle_self u _).symm
    · rw [unitFin_ideleAt_ne hu, Units.val_one, map_one]
      exact (finSingle_ne (fun e : u = w => hu (e ▸ h)) _).symm

theorem charAt_eq_locChar_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h hw x
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = ((Circle.toUnits (χ (locIdele F w _)) : ℂˣ) : ℂ)
  rw [GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw x]
  rfl

end GlobalTheory.LFun
