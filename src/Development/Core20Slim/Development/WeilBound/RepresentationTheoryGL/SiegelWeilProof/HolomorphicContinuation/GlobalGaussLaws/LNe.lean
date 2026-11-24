module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem lNe : LNe := by
  intro D ψ θ l hψ hθ hl τ
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ' : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hsk : IsSkew μ' := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  obtain ⟨lam2, hlam2, -, l', hl', habs⟩ := shift_char_realPar D ψ₀ h₀ θ hθ μ' hsk
  have hl2 : lam2 = lam := by
    apply (algebraMap D.host.F D.host.E).injective
    rw [hlam2, hμ']
    field_simp
  rw [hl2, ← hsh] at hl'
  have heq : l = l' := GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l l' hl hl'
  intro h
  have e := habs τ
  rw [← heq, h, abs_zero] at e
  have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 hxi
  have h2 : tauE D τ μ' ≠ 0 := (map_ne_zero _).2 hsk.1
  exact div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2) e.symm

end PositivityTheory.Rg.Sw.Glob
