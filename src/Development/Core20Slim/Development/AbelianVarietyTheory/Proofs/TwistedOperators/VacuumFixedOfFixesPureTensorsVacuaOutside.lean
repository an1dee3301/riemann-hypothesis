module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

theorem GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))), M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) →
    (∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) ψ → ψ = M.vac v := by
  intro F E _ _ _ _ _ σ n d Y Wd M om v k S hvac hstd hfix ψ hψ
  let ind : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

  let φ := Function.update ind v (M.vac v)
  have hφv : φ v = M.vac v := by simp [φ]
  have hφw : ∀ w, w ≠ v → φ w = ind w := fun w h => by simp [φ, h]
  have hφev : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton v).subset fun w hw => ?_
    by_contra hne
    exact hw (hφw w hne)
  have hSB : ∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; rw [hφv]; exact hvac
    · rw [hφw w h]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
  obtain ⟨r, hrinv, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφev
  have hupd : ∀ ψ₀, Function.update φ v ψ₀ = Function.update ind v ψ₀ :=
    fun ψ₀ => Function.update_idem _ _ _

  have hfixφ : om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    refine hfix f φ hSB fun w hw => ?_
    by_cases h : w = v
    · subst h; exact hφv
    · rw [hφw w h, hstd w hw]
  have hpv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    rw [hrt, hupd]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest
    refine ⟨hrinv, ?_⟩
    rw [hpv]
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hφev
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) ψ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    rw [← hψ r hRest, hpv, hfixφ]

  have hr0 : r 0 ≠ 0 := by
    have h1 := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at h1
    rw [h1, hupd]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have e1 : (fun i : Fin n × Fin d => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : Fin n × Fin d → AF F) i)) = 0 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : Fin n × Fin d → AF F) i).1 = 0
      exact map_zero _
    have e2 : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), Function.update ind v (fun _ => 1) w
        (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1 := by
      intro w
      by_cases h : w = v
      · subst h; simp
      · rw [Function.update_of_ne h]
        show Set.indicator {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
          (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1
        rw [Set.indicator_of_mem]
        · rfl
        · simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
          exact fun _ => zero_mem _
    rw [e1, finprod_congr e2, finprod_one, mul_one]
    exact hf
  funext y
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.EmbChart.atPlace v (y i)) := by
    intro u hu
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hrz : r (fun i => GlobalTheory.EmbChart.atPlace v (y i)) = r 0 := by
    simpa using hrinv 0 _ hz
  have h2 := congrFun key (fun i => GlobalTheory.EmbChart.atPlace v (y i))
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.EmbChart.evFin_atPlace, hrz] at h2
  exact mul_right_cancel₀ hr0 h2
