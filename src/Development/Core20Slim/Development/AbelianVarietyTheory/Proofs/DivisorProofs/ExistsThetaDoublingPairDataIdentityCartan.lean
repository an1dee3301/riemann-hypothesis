module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

open scoped Matrix ComplexOrder

namespace GlobalTheory.NormRatio

theorem gramAt_eq_one_of_gram {D : D7} (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold Formalism.BasicNotions.TH.gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem sig_snd_eq_zero_of_gram {D : D7} {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  by_contra hq
  let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
    Complex.one_re] at hk
  have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
    rw [Matrix.mul_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  linarith

theorem exists_ipPair_one : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  intro D cc δ t0 Q P X hX h1 h2
  obtain ⟨hF, hW⟩ := hX
  have gA := gramAt_eq_one_of_gram X.A hF.gramA
  have gB := gramAt_eq_one_of_gram X.B hF.gramB
  have hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := fun k =>
    ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hA : X.A.SigOK := hF.defA.1
  have hq := sig_snd_eq_zero_of_gram hF.gramA hA
  obtain ⟨cA, hc⟩ := GlobalTheory.Cusp.exists_isCartanFrame X.A hA
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank
  have hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1 := fun τ => by
    exact Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have rA := X.rkA
  have rB := X.rkB
  refine ⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩,
    (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩
  · rw [gA]; exact hI _
  · rw [gB]; exact hI _
  · have hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (X.A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hJ]; simp
  · rw [hone, gA]; simp
  · rw [hone, gA]; simp

end GlobalTheory.NormRatio
