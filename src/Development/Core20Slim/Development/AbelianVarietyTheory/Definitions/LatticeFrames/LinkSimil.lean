module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.StCheck

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


theorem link_simil {σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Link B L' ζ') : l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ * (B.L.gram * l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

end GlobalTheory.Unf.StCheck

end
