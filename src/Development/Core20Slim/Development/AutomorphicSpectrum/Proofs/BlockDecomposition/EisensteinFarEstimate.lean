module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.FarSeries

open PositivityTheory.RgEis PositivityTheory.Rg.SwEis Topology

theorem exp_mul_le {a b x s t L : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) (hL : |s - t| ≤ L) :
    Real.exp (x * s) ≤ Real.exp ((|a| + |b|) * L) * (Real.exp (a * t) + Real.exp (b * t)) := by
  have hx : |x| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have h3 : x * (s - t) ≤ (|a| + |b|) * L :=
    calc x * (s - t) ≤ |x * (s - t)| := le_abs_self _
      _ = |x| * |s - t| := abs_mul _ _
      _ ≤ (|a| + |b|) * L := mul_le_mul hx hL (abs_nonneg _) (by positivity)
  have h4 : Real.exp (x * t) ≤ Real.exp (a * t) + Real.exp (b * t) := by
    rcases le_total 0 t with ht | ht
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 ht)
      linarith [Real.exp_pos (a * t)]
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h1 ht)
      linarith [Real.exp_pos (b * t)]
  calc Real.exp (x * s) = Real.exp (x * (s - t)) * Real.exp (x * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := mul_le_mul (Real.exp_le_exp.2 h3) h4 (Real.exp_pos _).le (Real.exp_pos _).le

theorem summable_along {G G' : Type} [Group G] [Group G'] [TopologicalSpace G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (η : G' → ℝ) (hη : IsHt Γ' K' P' η) (x : ℝ)
    (hc : Conv Γ' P' fun g => x * η g) : Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := by
  let T : G' → ℂ := fun y => (Real.exp (x * η y) : ℂ)
  have hT : GlobalTheory.AutomorphicL2Unitary.LeftInv (P' ⊓ Γ') T := fun γ hγ y => by
    simp only [T, hη.left γ hγ.1 y, hη.rat γ hγ.2 hγ.1, zero_add]
  obtain ⟨-, h⟩ := GlobalTheory.StdUnn.cosetSum_along_mulEquiv G G' Φ P Γ P' Γ' hP hΓ T 1 1 (fun g => T (Φ g))
    (fun g => by simp) hT
  have h1 : GlobalTheory.Eis.CosetConv P' Γ' T (Φ (1 * 1)) := by
    refine (hc (Φ (1 * 1))).congr fun q => ?_
    show _ = ‖((Real.exp (x * η (rep q * Φ (1 * 1))) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ((h 1).1 h1).congr fun q => ?_
  show ‖((Real.exp (x * η (Φ (rep q * 1))) : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_one]

theorem bounded_of_law {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (Φ : G ≃ₜ* G')
    (P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (hK : IsCompact (K' : Set G')) (hPar : IsPar Γ' K' P' c)
    (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (f : G → ℂ) (hf : Continuous f) (hlaw : ∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image Φ.symm.continuous).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  obtain ⟨p, hp, k, hk, e⟩ := hPar.iwa (Φ x)
  have hx : x = Φ.symm p * Φ.symm k := by
    apply Φ.injective
    simp [e]
  have hq : Φ.symm p ∈ P := (hP _).2 (by simpa using hp)
  rw [hx, hlaw _ hq, Φ.apply_symm_apply, norm_mul, hPar.ch.norm p hp, one_mul]
  exact (hM _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)

theorem eFar : EFar := by
  intro hLip G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η R hK hPar hη hΓ hP hcv f hf hlaw
  have hsum : ∀ x : ℝ, R < x → Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := fun x hx =>
    summable_along Φ.toMulEquiv Γ P Γ' K' P' hΓ hP η hη x (hcv x hx)
  obtain ⟨M, hM0, hM⟩ := bounded_of_law Φ P Γ' K' P' c hK hPar hP f hf hlaw
  have key : ∀ a b : ℝ, R < a → R < b → ∀ C : Set G, IsCompact C → ∃ u : Cos P Γ → ℝ, Summable u ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ g ∈ C, ∀ q : Cos P Γ,
        ‖Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g)‖ ≤ u q := by
    intro a b ha hb C hC
    obtain ⟨L, hL⟩ := hLip G' Γ' K' P' η hK hPar.iwa hη (Φ '' C) (hC.image Φ.continuous)
    refine ⟨fun q => M * Real.exp ((|a| + |b|) * L) *
      (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q)))), ((hsum a ha).add (hsum b hb)).mul_left _, ?_⟩
    intro z h1 h2 g hg q
    have h3 := exp_mul_le (s := η (Φ (rep q * g))) (t := η (Φ (rep q))) (L := L) h1 h2
      (by rw [map_mul]; exact hL _ _ ⟨g, hg, rfl⟩)
    have h4 : (z * (η (Φ (rep q * g)) : ℂ)).re = z.re * η (Φ (rep q * g)) := by simp
    rw [norm_mul, Complex.norm_exp, h4]
    calc _ ≤ (Real.exp ((|a| + |b|) * L) * (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q))))) * M :=
          mul_le_mul h3 (hM _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcont : ∀ q : Cos P Γ, Continuous fun y : ℂ × G =>
      Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2) := fun q => by
    have h1 : Continuous fun y : ℂ × G => rep q * y.2 := continuous_const.mul continuous_snd
    have h2 : Continuous fun y : ℂ × G => ((η (Φ (rep q * y.2)) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hη.cont.comp (Φ.continuous.comp h1))
    exact (Complex.continuous_exp.comp (continuous_fst.mul h2)).mul (hf.comp h1)
  have hopen : ∀ a b : ℝ, IsOpen {z : ℂ | a < z.re ∧ z.re < b} := fun a b =>
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hab : ∀ z : ℂ, R < z.re → R < (R + z.re) / 2 ∧ R < z.re + 1 ∧ z ∈ {w : ℂ | (R + z.re) / 2 < w.re ∧ w.re < z.re + 1} :=
    fun z hz => ⟨by linarith, by linarith, by show _ ∧ _; constructor <;> linarith⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz C hC
    obtain ⟨u, hu, hb⟩ := key z.re z.re hz hz C hC
    exact ⟨u, hu, fun g hg q => hb z le_rfl le_rfl g hg q⟩
  · intro g z₀ hz₀
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 {g} isCompact_singleton
    have hd : DifferentiableOn ℂ (fun z => ∑' q : Cos P Γ, Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g))
        {w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} := by
      refine Complex.differentiableOn_tsum_of_summable_norm hu (fun q => ?_) (hopen _ _)
        (fun q w hw => hb w hw.1.le hw.2.le g rfl q)
      have : Differentiable ℂ fun z : ℂ => Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g) := by fun_prop
      exact this.differentiableOn
    exact (hd.differentiableAt ((hopen _ _).mem_nhds h3)).differentiableWithinAt
  · rintro ⟨z₀, g₀⟩ ⟨hz₀, -⟩
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨C', hC'c, hC'm⟩ := exists_compact_mem_nhds (Φ g₀)
    have hCm : Φ.symm '' C' ∈ 𝓝 g₀ := Filter.mem_of_superset (Φ.continuous.continuousAt.preimage_mem_nhds hC'm)
      fun x hx => ⟨Φ x, hx, by simp⟩
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 _ (hC'c.image Φ.symm.continuous)
    have hd : ContinuousOn (fun y : ℂ × G => ∑' q : Cos P Γ, Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2))
        ({w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} ×ˢ (Φ.symm '' C')) :=
      continuousOn_tsum (fun q => (hcont q).continuousOn) hu
        fun q y hy => hb y.1 hy.1.1.le hy.1.2.le y.2 hy.2 q
    exact (hd.continuousAt (prod_mem_nhds ((hopen _ _).mem_nhds h3) hCm)).continuousWithinAt
  · intro z γ hγ g
    refine GlobalTheory.Eis.leftInv_cosetSum (fun δ hδ x => ?_) γ hγ g
    have h1 : Φ δ ∈ P' := (hP δ).1 hδ.1
    have h2 : Φ δ ∈ Γ' := (hΓ δ).1 hδ.2
    simp only [hlaw δ hδ.1 x, map_mul, hη.left _ h1, hη.rat _ h2 h1, hPar.ch.rat _ h2 h1, zero_add, one_mul]

end GlobalTheory.CompanionTheory.FarSeries

end
