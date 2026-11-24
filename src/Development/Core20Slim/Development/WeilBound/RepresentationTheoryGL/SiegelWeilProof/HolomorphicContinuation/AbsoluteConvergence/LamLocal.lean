module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopSing
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

def invSub (Γ : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g}
  add_mem' := fun {F F'} hF hF' => ⟨hF.1.add hF'.1, fun γ hγ g => by simp [hF.2 γ hγ g, hF'.2 γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := fun a F hF => ⟨hF.1.const_smul a, fun γ hγ g => by simp [hF.2 γ hγ g]⟩

theorem lam_zero (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) : l 0 = 0 := by
  obtain ⟨C, -, hC⟩ := hG.Λbd l hl
  have h0 := hC 0 0 continuous_const (fun _ _ _ => rfl) (fun x _ => by simp)
  exact norm_le_zero_iff.mp h0

theorem lam_smul (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) (a : ℂ) (F : G → ℂ)
    (hF : Continuous F) (hFi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) : l (fun g => a * F g) = a * l F := by
  have h := hG.Λadd l hl a F 0 hF continuous_const hFi (fun _ _ _ => rfl)
  rw [lam_zero hG l hl, add_zero, add_zero] at h
  have hfun : (fun g => a * F g) = a • F := by
    funext g
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact h

theorem lam_local (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hs : s₀ ∈ U) (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g)
    (hEr : ∀ z : ℂ, σ < z.re → ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) g)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H s₀ ∧ H s₀ = l (I 1) ∧ ∀ᶠ z in 𝓝[≠] s₀, l (E z) = d.eval z * H z := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hEcont : ∀ z ∈ U, Continuous (E z) := by
    intro z hzU
    exact hEc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzU, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C U (fun z x => E z x) hUo
    (hEc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hEh x)
  have hfeq : ∀ z ∈ U, l (E z) = L (Φ z) := by
    intro z hzU
    have hmem : E z ∈ invSub Γ := ⟨hEcont z hzU, hEinv z hzU⟩
    rw [hL (E z) hmem (hEcont z hzU)]
    congr 1
    ext x
    rw [hΦ z hzU x]
    rfl
  have hfan : AnalyticOnNhd ℂ (fun z => l (E z)) U :=
    ((L.differentiable.comp_differentiableOn hΦd).congr hfeq).analyticOnNhd hUo
  obtain ⟨H, hHext, hHan, hHval⟩ := hG.Λval l hl
  refine ⟨H, hHan, hHval, ?_⟩
  have hext1 : GlobalTheory.Cont.IsExtAt (fun z => l (E z)) s₀ (fun z => l (E z)) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, hfan, ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hpoly : GlobalTheory.Cont.IsExtAt (fun z => d.eval z) s₀ (fun z => d.eval z) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, fun z _ => (Polynomial.differentiable d).analyticAt z,
      ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hmul := hpoly.mul hHext
  have hright : GlobalTheory.Cont.EqRight (fun z => l (E z))
      (fun s => d.eval s * l (GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (s - s₀) * sec 1 x))) := by
    obtain ⟨σ₁, hσ₁⟩ := hUr.1
    refine ⟨max σ σ₁, fun z hzr => ?_⟩
    have hzr' : max σ σ₁ < z.re := hzr
    have hz1 : σ < z.re := lt_of_le_of_lt (le_max_left _ _) hzr'
    have hzU : z ∈ U := hσ₁ (show σ₁ < z.re from lt_of_le_of_lt (le_max_right _ _) hzr')
    show l (E z) = d.eval z * l (GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z))
    obtain ⟨cs, hcsdef⟩ : ∃ cs, cs = GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) := ⟨_, rfl⟩
    rw [← hcsdef]
    have hE : ∀ g, E z g = d.eval z * cs g := by
      intro g
      rw [hEr z hz1 g, hcsdef]
    by_cases hd0 : d.eval z = 0
    · have hE0 : E z = 0 := funext fun g => by rw [hE g, hd0, zero_mul]; rfl
      rw [hE0, lam_zero hG l hl, hd0, zero_mul]
    · have hcs : cs = fun g => (d.eval z)⁻¹ * E z g := by
        funext g
        rw [hE g, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
      have hcsc : Continuous cs := by
        rw [hcs]
        exact continuous_const.mul (hEcont z hzU)
      have hcsi : ∀ γ ∈ Γ, ∀ g, cs (γ * g) = cs g := by
        intro γ hγ g
        rw [hcs]
        simp only
        rw [hEinv z hzU γ hγ g]
      have hEf : E z = fun g => d.eval z * cs g := funext hE
      rw [hEf, lam_smul hG l hl _ cs hcsc hcsi]
  exact (hext1.congr hright).eventuallyEq hmul

end PositivityTheory.Rg.Sw.AbsSt.Vac
