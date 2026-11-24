module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilIntegralIdentityStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicSiegelWeilIntegralIdentityStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFiniteStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFiniteStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsiStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSchwartzFunctionIntegrableStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx db hdb Φ hΦ
  obtain ⟨μ₁, μ₂, c, h1, h2, s1, s2, hc, hme, hmap⟩ := GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n dx hdx.1
  obtain ⟨ν₁, ν₂, c', g1, g2, t1, t2, hc', hme', hmap'⟩ := GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n db hdb.1
  obtain ⟨k, P, Q, hP, hQ, hsum⟩ := id hΦ
  have hpureSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat
      (fun X : Fin n → Fin M → AF F ⊗[F] E => P i (projInf X) * Q i (projFin X)) := fun i =>
    GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod (hP i) (hQ i) fun _ => rfl
  have hfac : ∀ i (b : HermR (AF F) σ n), starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
      (c.toReal : ℂ) * (starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) (hermInf σ b) *
        starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) (hermFin σ b)) := by
    intro i b
    let A : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun x =>
      P i x * psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
          gramR (Ainf F) σ J x)))
    let B : (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun y =>
      Q i y * psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
          gramR (Af F) σ J y)))
    let G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun z => A z.1 * B z.2
    have e1 : starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
        ∫ X, G (projInf X, projFin X) ∂dx := by
      unfold starN
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      show _ * _ = G _
      rw [GlobalTheory.T.character_trace_pairing_eq_inner_psi F E σ hCM M J n ψ b X]
      simp only [G, A, B]
      ring
    have e2 := hme.integral_map (μ := dx) G
    have e3 : ∫ z, G z ∂μ₁.prod μ₂ = (∫ x, A x ∂μ₁) * ∫ y, B y ∂μ₂ := integral_prod_mul A B
    rw [e1]
    refine e2.symm.trans ?_
    rw [hmap, integral_smul_measure, e3, Complex.real_smul]
    rfl
  have hpure : ∀ i, Integrable (starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X))) db := by
    intro i
    have hA := GlobalTheory.T.archimedean_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₁ h1 ν₁ g1 (P i) (hP i)
    have hB := GlobalTheory.T.finite_adelic_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₂ h2 ν₂ g2 (Q i) (hQ i)
    have hAB := hA.mul_prod hB
    have hAB' : Integrable (fun z : HermR (Ainf F) σ n × HermR (Af F) σ n =>
        starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) z.1 * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) z.2)
        (db.map (fun b => (hermInf σ b, hermFin σ b))) := by
      rw [hmap']
      exact hAB.smul_measure hc'
    have := (hme'.integrable_map_iff.1 hAB').const_mul (c.toReal : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    exact (hfac i b).symm
  have hdec : starN σ J ψ dx Φ = fun b => ∑ i, starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b := by
    funext b
    unfold starN
    rw [← integral_finsetSum _ fun i _ => GlobalTheory.T.twisted_schwartz_function_integrable F E σ hCM M J n ψ hψ dx hdx.1 _ (hpureSB i) b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Φ X * _ = _
    rw [hsum, Finset.sum_mul]
  rw [hdec]
  exact integrable_finsetSum _ fun i _ => hpure i

end GlobalTheory.CompanionTheory.SiegelND.Integ
