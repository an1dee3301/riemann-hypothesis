module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealParOfIsCharAF
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob


set_option synthInstance.maxHeartbeats 400000 in
theorem realPar_explicit (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ a : D.host.F, a ≠ 0 ∧
      HasRealPar ψ θ (fun τ => -(tauE D τ (algebraMap D.host.F D.host.E a)).re) ∧
      ∀ τ, (tauE D τ (algebraMap D.host.F D.host.E a)).im = 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine ⟨a, ha0, ?_, hreal⟩
  intro x
  have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
    simp only [psiInf]
    rw [ha]
    congr 1
    show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
    rw [mul_zero]; rfl
  rw [e1, h₀.2.2 θ hθ]
  congr 1
  have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
    intro ρ
    have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
        ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
    rw [e3, map_mul, (hθ ρ).1]
  simp only [e2]
  have e5 : ∀ ρ, (((tauE D ρ (algebraMap D.host.F D.host.E a)).re : ℝ) : ℂ) = tauE D ρ y := by
    intro ρ
    have h := hreal ρ
    rw [hy_def] at h ⊢
    apply Complex.ext
    · simp
    · simp [h]
  simp only [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [e5 ρ]
  ring

theorem lNZ : LNZ := by
  intro D ψ θ l hψ hθ hl τ
  obtain ⟨a, ha0, hl0, hre⟩ := realPar_explicit D ψ hψ θ hθ
  have e : l = _ := GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l _ hl hl0
  rw [e]
  intro h0
  apply ha0
  have h1 : tauE D τ (algebraMap D.host.F D.host.E a) = 0 := by
    apply Complex.ext
    · simpa using h0
    · simpa using hre τ
  have h2 : algebraMap D.host.F D.host.E a = 0 := (map_eq_zero _).1 h1
  exact (map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).1 h2

end PositivityTheory.Rg.Sw.Glob
