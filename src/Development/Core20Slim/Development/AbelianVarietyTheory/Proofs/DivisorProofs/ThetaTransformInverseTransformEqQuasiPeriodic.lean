module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicFourierSeriesOfSummableCoefficients
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
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
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem thV_invV_eq : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec
  have hC' := hC
  obtain ⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩ := hC'
  funext w
  obtain ⟨x, y⟩ := w
  let P : (Fin N → AF F) → ℂ := fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))
  have hPc : Continuous P := by
    refine (hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)
    refine (continuous_const.mul ?_).neg
    fun_prop
  have hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u := fun ξ u => integrand_periodic hq x u ξ
  have hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) =
      invV ψ ν 𝓓 f (rat ξ + x) := by
    intro ξ
    unfold invV
    congr 1
    funext u
    have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
    have h := hq ξ 0 (x, u)
    rw [h0, Prod.mk_add_mk, zero_add] at h
    rw [h, Bd_half]
    simp only [P]
    rw [mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]
    linear_combination two_mul_invOf (rat ξ ⬝ᵥ u)
  have hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖) :=
    (GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x
  have hser := GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P
    (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y
  have hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) := by
    simp only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  rw [hfxy, hser, ← tsum_mul_right]
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  refine tsum_congr fun ξ => ?_
  show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _
  rw [Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]
  ring

end GlobalTheory.ThetaTransform
