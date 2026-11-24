module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignature
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Model

variable {D : D7}

abbrev nLine (D : D7) : HSp D := GlobalTheory.Doubling.hneg (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1)

theorem isLineVec_nLine {c : D.host.E} (hc : c ≠ 0) : IsLineVec (nLine D) (fun _ => c) := by
  refine ⟨rfl, ?_⟩
  have h : ∀ i j : Fin 1, (nLine D).gram i j = -1 := fun i j => by
    show -((Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram i j) = -1
    rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
    simp [Examples₂.sgn]
  change ∑ i : Fin 1, star c * ∑ j : Fin 1, (nLine D).gram i j * c ≠ 0
  simp [h, hc]

open GlobalTheory.ChainOnto (Com PiLocalization₂)


end GlobalTheory.SeeSaw.Model

end
