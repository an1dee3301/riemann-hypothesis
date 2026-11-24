module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Batteries.Logic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Push
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section Rat

variable {T L : Type} [Field L] (σ : L →+* ℂ) (t₀ : T)

def RatIn (f : T → ℂ) : Prop := ∀ t, f t ≠ 0 ∧ ∃ y : Lˣ, σ y = f t / f t₀

variable {σ t₀}

theorem RatIn.mul {f g : T → ℂ} (hf : RatIn σ t₀ f) (hg : RatIn σ t₀ g) : RatIn σ t₀ fun t => f t * g t := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  obtain ⟨hg0, z, hz⟩ := hg t
  refine ⟨mul_ne_zero hf0 hg0, y * z, ?_⟩
  rw [Units.val_mul, map_mul, hy, hz, mul_div_mul_comm]

theorem RatIn.inv {f : T → ℂ} (hf : RatIn σ t₀ f) : RatIn σ t₀ fun t => (f t)⁻¹ := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  refine ⟨inv_ne_zero hf0, y⁻¹, ?_⟩
  rw [map_units_inv, hy, inv_div, inv_div_inv]

theorem ratIn_const {κ : ℂ} (h : κ ≠ 0) : RatIn σ t₀ fun _ => κ := by
  intro _
  exact ⟨h, 1, by rw [Units.val_one, map_one, div_self h]⟩

theorem ratIn_of_unit {f : T → ℂ} (h : ∀ t, ∃ y : Lˣ, σ y = f t) : RatIn σ t₀ f := by
  intro t
  obtain ⟨y, hy⟩ := h t
  obtain ⟨y₀, hy₀⟩ := h t₀
  refine ⟨hy ▸ (map_ne_zero σ).2 y.ne_zero, y * y₀⁻¹, ?_⟩
  rw [Units.val_mul, map_mul, map_units_inv, hy, hy₀, div_eq_mul_inv]

theorem RatIn.of_mul {f g u : T → ℂ} (hg : RatIn σ t₀ g) (hu : RatIn σ t₀ u) (h : ∀ t, f t * u t = g t) : RatIn σ t₀ f := by

  have e : f = fun t => g t * (u t)⁻¹ := funext fun t => by rw [← h t, mul_inv_cancel_right₀ (hu t).1]
  rw [e]
  exact hg.mul hu.inv

end Rat

variable {D : D7}

section Factor

variable {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

def Factor (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧
    ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
      (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))),
      Function.Surjective p ∧ (∀ t, Function.Injective (J t)) ∧
      (∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) ∧
      (∀ t P, X.I ψ θ t P = lam t • J t (p P)) ∧
      (∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I' ψ θ t P' = J t (p' P')) ∧
      ∃ P', p' P' ≠ 0 ∧ ∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m'

variable {X ψ θ}

theorem Factor.isConst [Nonempty T] {lam : T → ℂ} (h : Factor X ψ θ lam) : X.IsConst ψ θ lam := by
  unfold Factor at h
  obtain ⟨hlam, Pi, p, p', J, hp, hJ, hint, hI, hI', P', hP', hint'⟩ := h

  obtain ⟨P, hPP⟩ := hp (p' P')
  unfold Tri.IsConst
  refine ⟨⟨Classical.arbitrary T, hlam _⟩, P, P', fun t => ⟨fun h => ⟨hint t P h, hint' t h⟩, ?_, fun h => ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    apply hP'
    apply hJ t
    rw [map_zero, ← hI' t P' (hint' t)]
    funext h
    exact hcon h
  · rw [hI t P, hI' t P' (hint' t), hPP]
    rfl

theorem Factor.eq_mul {lam c : T → ℂ} (h : Factor X ψ θ lam) (hc : X.IsConst ψ θ c) : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ t, c t = κ * lam t := by
  unfold Factor at h
  unfold Tri.IsConst at hc
  obtain ⟨hlam, Pi, p, p', J, -, hJ, -, hI, hI', -⟩ := h
  obtain ⟨⟨t₁, ht₁⟩, P, P', hc⟩ := hc

  have key : ∀ t, lam t • p P = c t • p' P' := by
    intro t
    obtain ⟨hi, -, heq⟩ := hc t
    apply hJ t
    rw [map_smul, map_smul, ← hI t P, ← hI' t P' (fun h => (hi h).2)]
    funext h
    exact heq h
  have hne : p' P' ≠ 0 := by
    intro h0
    obtain ⟨hi, ⟨h₁, hh₁⟩, -⟩ := hc t₁
    apply hh₁
    rw [hI' t₁ P' (fun h => (hi h).2), h0, map_zero]
    rfl
  have hq : ∀ t, p P = ((lam t)⁻¹ * c t) • p' P' := by
    intro t
    rw [← smul_smul, ← key t, inv_smul_smul₀ (hlam t)]
  refine ⟨(lam t₁)⁻¹ * c t₁, mul_ne_zero (inv_ne_zero (hlam t₁)) ht₁, fun t => ?_⟩
  have e := smul_left_injective ℂ hne ((hq t).symm.trans (hq t₁))
  rw [← e]
  field_simp [hlam t]

end Factor

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks}

def NegIdx (V : HSp D) (q : ℕ) : Prop := ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) (V.rank - q) q

end GlobalTheory.ConstRatio

end
