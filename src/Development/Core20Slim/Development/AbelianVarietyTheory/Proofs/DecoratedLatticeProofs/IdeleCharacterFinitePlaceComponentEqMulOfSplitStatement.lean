module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplit
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | exact GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_mul_locChar <;> assumption)
