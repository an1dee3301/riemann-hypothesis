module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import ReciprocityTheory.Automorphisms.Unitary

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitFrameW


theorem complMap_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E)
    (c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E) (hc : Continuous c)
    (hci : ∀ x : E, c (s.i x) = algebraMap E _ x) (h : s.w.under (𝓞 (maximalRealSubfield E)) = s.v)
    (a : s.v.adicCompletion (maximalRealSubfield E)) : GlobalTheory.LFun.complMap h a = c a := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).equalizer
    (GlobalTheory.LFun.SplitChart.continuous_complMap h) hc (funext fun k => ?_)) a
  change GlobalTheory.LFun.complMap h (algebraMap _ _ k) = c (algebraMap _ _ k)
  rw [GlobalTheory.LFun.complMap_algebraMap, ← hci]
  congr 1
  exact s.i.commutes k

theorem under_w {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E) :
    s.w.under (𝓞 (maximalRealSubfield E)) = s.v :=
  HeightOneSpectrum.ext s.w_under

theorem cpt_swap {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E)
    (Φ : FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E →+* FiniteAdeleRing (𝓞 E) E)
    (hΦ : ∀ (a : FiniteAdeleRing (𝓞 F1) F1) (x : E),
      Φ (a ⊗ₜ[F1] x) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F1 E a)
    (s : SplitPlace E) (c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E)
    (hc : Continuous c) (hci : ∀ x : E, c (s.i x) = algebraMap E _ x) (y : AL E) :
    Φ ((swapCast hF).symm y) s.w = c (s.proj y) := by
  subst hF
  induction y using TensorProduct.induction_on with
  | zero =>
    simp
    rfl
  | add y z hy hz =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ← hy, ← hz]
    rfl
  | tmul x a =>
    change Φ (a ⊗ₜ x) s.w = c (s.i x * ReciprocityTheory.Aut.evalAt E s.v a)
    rw [hΦ, map_mul, hci]
    change algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap _ E a s.w = _
    rw [GlobalTheory.DefU.ClassFin.adMap_eq_complMap (under_w s), complMap_eq s c hc hci]
    rfl

end GlobalTheory.SplitFrameW

namespace GlobalTheory.SplitFrameW



end GlobalTheory.SplitFrameW
