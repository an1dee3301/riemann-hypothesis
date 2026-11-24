module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem rder_zero (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (0 : GA D V → ℂ) = 0 := by
  funext g
  simp [Rder]

theorem rderC_zero (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (0 : GA D V → ℂ) = 0 := by
  simp [RderC, rder_zero]

theorem gelf_zero (τ : D.what₂.Tau) (k : ℕ) : gelf θ V τ k (0 : GA D V → ℂ) = 0 := by
  unfold gelf
  refine Finset.sum_eq_zero fun idx _ => ?_
  have h : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, f 0 = 0) →
      l.foldr (fun f acc => f acc) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons f l ih =>
      rw [List.foldr_cons, ih (fun f' hf' => hl f' (by simp [hf']))]
      exact hl f (by simp)
  apply h
  intro f hf
  rw [List.mem_ofFn] at hf
  obtain ⟨a, rfl⟩ := hf
  exact rderC_zero θ V τ _

theorem foldr_rder_zero (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, ih]
    exact rder_zero θ V p.1 p.2

theorem isAutFunSm_zero : IsAutFunSm θ V (fun _ => 0) := {
  left _ _ _ := rfl
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const
  zfin := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun τ k f hf => ?_⟩
    rw [Submodule.mem_bot] at hf
    subst hf
    rw [gelf_zero]
    exact Submodule.zero_mem _
  growth := by
    refine ⟨0, fun l _ x => ⟨0, fun g _ => ?_⟩⟩
    have h := foldr_rder_zero θ V l
    change ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ)) (x * g)‖ ≤ _
    rw [h]
    simp }

theorem isCuspFun_zero : IsCuspFun V (fun _ => 0) := by
  intro r C _ μ 𝓕 _ _ g
  simp

variable {V} {S : D.what₂.Tau → SPar}



variable (V) in
theorem rder_smul (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  first
    | exact deriv_const_mul_field c
    | simp

variable (V) in
theorem foldr_rder_smul (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact rder_smul θ V p.1 p.2 c _


variable (V) in
theorem isAutFunSm_smul {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (c : ℂ) : IsAutFunSm θ V (c • φ) := {
  left γ hγ g := by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k hk1 hk2 g => by simp only [Pi.smul_apply, hk k hk1 hk2 g]⟩
  cont := h.cont.const_smul c
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, hW, hφ, hg⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c hφ, hg⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [foldr_rder_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c) }


variable (V) in
theorem isCuspFun_smul {φ : GA D V → ℂ} (h : IsCuspFun V φ) (c : ℂ) : IsCuspFun V (c • φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simp only [Pi.smul_apply]
  rw [MeasureTheory.integral_smul, h r C hC μ 𝓕 hμ h𝓕 g, smul_zero]


end Formalism.IndefR.Mult

end
