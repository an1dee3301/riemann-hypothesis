module

public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecompositionStatement
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Pi

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

theorem scalar_wall (hSec : SecLaw) (hWL : WallLaw) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ K P : Subgroup G) (c : G → ℂ) (η β : G → ℝ) (hK : IsCompact (K : Set G)) (hP : IsPar Γ K P c)
    (hη : IsHt Γ K P η) (hβ : IsHt Γ K P β) (hW : AllRep K fun ρ => HasWall Γ K P P c η η β ρ) (f : G → ℂ) (u : ℂ)
    (hf : Continuous f) (hlaw : ∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G))))) :
    ∃ (R : ℝ) (D : ℂ → ℂ) (H : ℂ → G → ℂ), Differentiable ℂ D ∧ (∃ z, D z ≠ 0) ∧ (∀ g, Differentiable ℂ (H · g)) ∧
      Continuous (fun y : ℂ × G => H y.1 y.2) ∧
      (∀ x : ℝ, R < x → Conv Γ P fun g => x * η g) ∧ (∀ x : ℝ, x < -R → Conv Γ P fun g => β g - x * η g) ∧
      (∀ a b : ℝ, R < a → b < -R → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g,
        ‖H z g‖ ≤ M * (pos Γ P (fun x => a * η x) g + pos Γ P (fun x => β x - b * η x) g)) ∧
      ∀ z : ℂ, R < z.re → ∀ g, HasSum (fun q : Cos P Γ =>
        D z * (Complex.exp ((z - u) * η (rep q * g)) * f (rep q * g))) (H z g) := by
  have h1 : η 1 = 0 := by
    have := hη.left 1 (one_mem _) 1
    simp only [mul_one] at this
    linarith
  have hzero : ∀ r ∈ P, r ∈ K → η r = 0 := fun r _ hr => by
    have := hη.right 1 r hr
    rwa [one_mul, h1] at this
  obtain ⟨d, ρ, w, e, hρ, hw, he⟩ := GlobalTheory.T.finite_K_type_decomposition G Γ K P c η hP.ch hzero
    (fun p hp q _ => hη.left p hp q) f u hf hlaw hfin
  obtain ⟨R, D, Op, H, hWl⟩ := hW (Fin d → ℂ) ρ hρ
  obtain ⟨hs₁, -, M₀, hM₀⟩ := hSec G (Fin d → ℂ) K ρ hK hρ Γ P c hP
  obtain ⟨-, -, hbd⟩ := hWL G (Fin d → ℂ) K ρ hK hρ Γ P P c η η β _ R D Op H hP hP hη hη hβ hWl
  let w' : secSp K P c ρ := ⟨w, hw⟩
  have hsec : ∀ y, f y = Complex.exp (u * η y) * e (sec K P c ρ y w) := by
    intro y
    obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa y
    rw [hs₁ w hw p hp ⟨k, hk⟩ |> fun h => (by simpa using h : sec K P c ρ (p * k) w = c p • ρ (⟨k, hk⟩ : K)⁻¹ w)]
    rw [map_smul, he, hlaw p hp k, hη.right p k hk, smul_eq_mul]
    ring
  refine ⟨R, D, fun z g => e (H z g w'), hWl.dEnt.1, hWl.dNe, fun g => ?_, ?_, hWl.convR, hWl.convL, ?_, ?_⟩
  · exact e.differentiable.comp ((hWl.hol g).clm_apply (differentiable_const _))
  · exact e.continuous.comp (hWl.cont.clm_apply continuous_const)
  · intro a b ha hb
    obtain ⟨M, hM⟩ := hbd a b ha hb
    refine ⟨‖e‖ * M * ‖w'‖, fun z h₁ h₂ g => ?_⟩
    have q₁ := e.le_opNorm (H z g w')
    have q₂ := (H z g).le_opNorm w'
    have q₃ := hM z h₁ h₂ g
    calc ‖e (H z g w')‖ ≤ ‖e‖ * ‖H z g w'‖ := q₁
      _ ≤ ‖e‖ * (‖H z g‖ * ‖w'‖) := by gcongr
      _ ≤ ‖e‖ * ((M * _) * ‖w'‖) := by gcongr
      _ = _ := by ring
  · intro z hz g
    have hconv := hWl.convR z.re hz g
    have hsum : Summable fun q : Cos P Γ => Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w := by
      refine Summable.of_norm_bounded (g := fun q : Cos P Γ => Real.exp (z.re * η (rep q * g)) * (M₀ * ‖w‖)) (hconv.mul_right _) fun q => ?_
      rw [norm_smul, Complex.norm_exp]
      have : ((z * (η (rep q * g) : ℂ))).re = z.re * η (rep q * g) := by simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (hM₀ _ _) (Real.exp_pos _).le
    have h2 : HasSum (fun q : Cos P Γ => D z • (Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w)) (H z g w') := by
      have := hsum.hasSum.const_smul (D z)
      rwa [show (∑' q : Cos P Γ, Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w) =
        eis Γ K P c ρ (fun x => z * η x) g w from rfl, ← show H z g w' = D z • eis Γ K P c ρ (fun x => z * η x) g w from hWl.eqR z hz g w'] at this
    have h3 := e.hasSum h2
    have e2 : (fun q : Cos P Γ => e (D z • (Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w))) =
        fun q => D z * (Complex.exp ((z - u) * η (rep q * g)) * f (rep q * g)) := by
      funext q
      have e3 : Complex.exp (z * η (rep q * g)) = Complex.exp ((z - u) * η (rep q * g)) * Complex.exp (u * η (rep q * g)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hsec (rep q * g), map_smul, map_smul, smul_eq_mul, smul_eq_mul, e3]
      ring
    have h4 : HasSum (fun q : Cos P Γ => e (D z • (Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w))) (e (H z g w')) := h3
    rw [e2] at h4
    exact h4

theorem hasSum_cos {G U X : Type} [Group G] [Group U] [AddCommMonoid X] [TopologicalSpace X] (Φ : G ≃* U)
    (Γ P : Subgroup G) (Γ' P' : Subgroup U) (hΓ : ∀ x, x ∈ Γ ↔ Φ x ∈ Γ') (hP : ∀ x, x ∈ P ↔ Φ x ∈ P') (T : U → X)
    (hT : ∀ γ ∈ Γ', γ ∈ P' → ∀ y, T (γ * y) = T y) (y : U) (S : X)
    (h : HasSum (fun q : Cos P' Γ' => T (rep q * y)) S) :
    HasSum (fun q : Cos P Γ => T (Φ (rep q) * y)) S := by
  let m : Γ → Γ' := fun γ => ⟨Φ γ.1, (hΓ _).1 γ.2⟩
  have hrel : ∀ a b : Γ, QuotientGroup.rightRel (P.subgroupOf Γ) a b ↔ QuotientGroup.rightRel (P'.subgroupOf Γ') (m a) (m b) := by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hP]
    simp [m]
  let g : Cos P Γ → Cos P' Γ' := Quotient.map' m fun a b hab => (hrel a b).1 hab
  have hinj : Function.Injective g := by
    intro q₁ q₂
    induction q₁ using Quotient.inductionOn' with | h a => ?_
    induction q₂ using Quotient.inductionOn' with | h b => ?_
    intro e
    exact Quotient.sound' ((hrel a b).2 (Quotient.exact' e))
  have hsurj : Function.Surjective g := by
    intro q
    induction q using Quotient.inductionOn' with | h a => ?_
    refine ⟨Quotient.mk'' ⟨Φ.symm a.1, (hΓ _).2 (by simpa using a.2)⟩, ?_⟩
    show Quotient.mk'' (m _) = _
    congr 1
    apply Subtype.ext
    simp [m]
  have h2 := ((Equiv.ofBijective g ⟨hinj, hsurj⟩).hasSum_iff).2 h
  have e : ((fun q => T (rep q * y)) ∘ (Equiv.ofBijective g ⟨hinj, hsurj⟩)) = fun q : Cos P Γ => T (Φ (rep q) * y) := by
    funext q
    have e1 : (Quotient.mk'' (Quotient.out (g q)) : Cos P' Γ') = Quotient.mk'' (m (Quotient.out q)) := by
      rw [Quotient.out_eq']
      show g q = g (Quotient.mk'' (Quotient.out q))
      rw [Quotient.out_eq']
    have e2 := Quotient.exact' e1
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at e2
    have e3 : Φ (rep q) * y = (((m (Quotient.out q)) * (Quotient.out (g q))⁻¹ : Γ') : U) * (rep (g q) * y) := by
      show _ = (Φ (Quotient.out q).1 * (Quotient.out (g q)).1⁻¹) * ((Quotient.out (g q)).1 * y)
      simp [rep, mul_assoc]
    rw [e3, hT _ (Subtype.coe_prop _) e2]
    rfl
  rw [e] at h2
  exact h2


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}





end GlobalTheory.CompanionTheory.SiegelFrame
