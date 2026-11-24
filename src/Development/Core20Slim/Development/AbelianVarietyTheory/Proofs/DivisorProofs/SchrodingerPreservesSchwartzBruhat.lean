module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerAlt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrSB

theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterativeScalingBound.main
  | exact _root_.GlobalTheory.IterativeScalingBound.main
  | (apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterativeScalingBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterativeScalingBound.main ..)

theorem isLocallyConstant_addChar {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    (ψ : AddChar G ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hU : (⇑ψ) ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : G) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact Metric.ball_mem_nhds _ (by norm_num)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU
  have hker : ∀ y ∈ V, ψ y = 1 := by
    intro y hy
    apply eq_one_of_pow_two_pow
    intro k
    have hm : (2 ^ k) • y ∈ V := V.toAddSubgroup.nsmul_mem hy _
    have := hV hm
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0) := by
    have h := ((continuous_sub_right x).tendsto x)
    rwa [sub_self] at h
  filter_upwards [hx (V.isOpen.mem_nhds V.zero_mem)] with y hy
  have e : y = x + (y - x) := by abel
  rw [e, AddChar.map_add_eq_mul, hker _ hy, mul_one]

theorem continuous_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have h : Continuous (GlobalTheory.LatVac.liftV v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp h

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ GlobalTheory.WeilM.SB _ := by
  intro F _ _ κ _ ψ hψ v w φ hφ
  have hloc := isLocallyConstant_addChar _ (continuous_psiAt ψ hψ v)
  have hlin : Continuous fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  refine ⟨?_, ?_⟩
  · exact (hloc.comp_continuous hlin).mul (hφ.1.comp_continuous (continuous_add_const w.1))
  · have hc : HasCompactSupport fun x : κ → Fv F v => φ (x + w.1) :=
      hφ.2.comp_homeomorph (Homeomorph.addRight w.1)
    exact hc.mul_left (f := fun x => GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)))

end GlobalTheory.SchrSB
