module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraExtra
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrodTheta

variable {F : Type} [Field F] [NumberField F]

def HasTheta {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) (f : W → ℂ) : Prop :=
  ∀ x, HasSum (fun ξ : κ → F => co.rho ψ x Φ fun i => algebraMap F (AF F) (ξ i)) (f x)

def IsPureSum {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (φ₀ : (κ → Fv F v₁) → ℂ) (Φ : (κ → AF F) → ℂ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    Φ = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in cofinite, φ k v = vac v) ∧
      ∀ k, φ k v₁ = φ₀

theorem isPureSum_zero {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ)
    (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Fv F v₁) → ℂ) : IsPureSum vac v₁ φ₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩

theorem IsPureSum.smul {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ) (c : ℂ) :
    IsPureSum vac v₁ φ₀ (c • Φ) := by
  obtain ⟨m, f, φ, rfl, h1, h2, h3⟩ := h
  refine ⟨m, fun k => c • f k, φ, ?_, h1, h2, h3⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  ring

theorem IsPureSum.add {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ Ψ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ)
    (h' : IsPureSum vac v₁ φ₀ Ψ) : IsPureSum vac v₁ φ₀ (Φ + Ψ) := by
  first
  | exact @_root_.GlobalTheory.ClosingLemmaThird.main
  | exact _root_.GlobalTheory.ClosingLemmaThird.main
  | (apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemmaThird.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemmaThird.main ..)

theorem IsPureSum.sum {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ k ∈ s, IsPureSum vac v₁ φ₀ (Φ k)) : IsPureSum vac v₁ φ₀ (∑ k ∈ s, Φ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPureSum_zero vac v₁ φ₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

section Theta

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
  (co : Darboux B κ) (ψ : AddChar (AF F) ℂ)

theorem rho_smul (x : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : co.rho ψ x (c • Φ) = c • co.rho ψ x Φ := by
  funext y
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasTheta_zero : HasTheta co ψ 0 0 := fun x => by
  have : co.rho ψ x 0 = 0 := by simpa using rho_smul co ψ x 0 0
  simpa [this] using (hasSum_zero : HasSum (fun _ : κ → F => (0 : ℂ)) 0)

variable {co ψ}

theorem HasTheta.smul {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (c : ℂ) :
    HasTheta co ψ (c • Φ) (c • f) := fun x => by
  rw [rho_smul]
  exact (h x).mul_left c

theorem HasTheta.add {Φ Ψ : (κ → AF F) → ℂ} {f g : W → ℂ} (h : HasTheta co ψ Φ f) (h' : HasTheta co ψ Ψ g) :
    HasTheta co ψ (Φ + Ψ) (f + g) := by
  intro x
  have h0 := (h x).add (h' x)
  simpa only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, mul_add] using h0

theorem HasTheta.sum {ι : Type} (s : Finset ι) {Φ : ι → (κ → AF F) → ℂ} {f : ι → W → ℂ}
    (h : ∀ k ∈ s, HasTheta co ψ (Φ k) (f k)) : HasTheta co ψ (∑ k ∈ s, Φ k) (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasTheta_zero co ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem HasTheta.thetaSum_eq {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (x : W) :
    thetaSum F (co.rho ψ x Φ) = f x :=
  (h x).tsum_eq

end Theta

end GlobalTheory.SchrodTheta

end
