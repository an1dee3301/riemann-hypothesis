module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NoInvPairing

variable {p q r s : ℕ} {T₂ : GrpData r s}

abbrev Pairing (p q : ℕ) (R : DSRep T₂) : Type :=
  Pol p q r s →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] ℂ

def IsInvPairing {p q : ℕ} (R : DSRep T₂) (b : Pairing p q R) : Prop :=
  ∀ Z ∈ upq r s, ∀ P y, b (fockAct2 p q r s Z P) y + b P (R.HK.act Z y) = 0

def invSub (p q : ℕ) (R : DSRep T₂) : Submodule ℂ (Pairing p q R) where
  carrier := {b | IsInvPairing R b}
  zero_mem' := by intro Z _ P y; simp
  add_mem' := by
    intro a b ha hb Z hZ P y
    have h1 := ha Z hZ P y
    have h2 := hb Z hZ P y
    simp only [LinearMap.add_apply]
    linear_combination h1 + h2
  smul_mem' := by
    intro c b hb Z hZ P y
    have h1 := hb Z hZ P y
    simp only [LinearMap.smul_apply, smul_eq_mul]
    linear_combination c * h1

variable (R : DSRep T₂)

theorem fock_comm (Z : Mat p q) (W : Mat r s) (P : Pol p q r s) :
    fockAct1 p q r s Z (fockAct2 p q r s W P) = fockAct2 p q r s W (fockAct1 p q r s Z P) := by
  have hc := (GlobalTheory.FockAlg.fock_lie_and_commute p q r s).2.2.2 Z W
  simpa using LinearMap.congr_fun hc P

def pre1 (Z : Mat p q) : invSub p q R →ₗ[ℂ] invSub p q R where
  toFun b := ⟨b.1 ∘ₗ fockAct1 p q r s Z, by
    intro W hW P y
    have hb : IsInvPairing R b.1 := b.2
    have := hb W hW (fockAct1 p q r s Z P) y
    simp only [LinearMap.comp_apply]
    rw [fock_comm]
    exact this⟩
  map_add' a b := by apply Subtype.ext; ext P y; simp
  map_smul' c b := by apply Subtype.ext; ext P y; simp

theorem invariantFockPairingPrecompAction_add (Z W : Mat p q) (b : invSub p q R) :
    pre1 R (Z + W) b = pre1 R Z b + pre1 R W b := by
  apply Subtype.ext; ext P y; simp [pre1]

theorem invariantFockPairingPrecompAction_smul (c : ℂ) (Z : Mat p q) (b : invSub p q R) :
    pre1 R (c • Z) b = c • pre1 R Z b := by
  apply Subtype.ext; ext P y; simp [pre1]

theorem invariantFockPairingPrecompAction_commutator (Z W : Mat p q) (b : invSub p q R) :
    pre1 R (Z * W - W * Z) b = pre1 R W (pre1 R Z b) - pre1 R Z (pre1 R W b) := by
  have hl := (GlobalTheory.FockAlg.fock_lie_and_commute p q r s).2.1 Z W
  apply Subtype.ext; ext P y
  simp [pre1, hl]

def evalB (P : Pol p q r s) (y : R.HK.V) : Module.Dual ℂ (invSub p q R) where
  toFun b := b.1 P y
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem dualMap_evalB (Z : Mat p q) (P : Pol p q r s) (y : R.HK.V) :
    (pre1 R Z).dualMap (evalB R P y) = evalB R (fockAct1 p q r s Z P) y := by
  ext b; rfl

def MM (p q : ℕ) : Submodule ℂ (Module.Dual ℂ (invSub p q R)) :=
  Submodule.span ℂ (Set.range fun x : Pol p q r s × R.HK.V => evalB R x.1 x.2)

theorem evalB_mem (P : Pol p q r s) (y : R.HK.V) : evalB R P y ∈ MM R p q :=
  Submodule.subset_span ⟨(P, y), rfl⟩

theorem dualMap_mem (Z : Mat p q) : ∀ φ ∈ MM R p q, (pre1 R Z).dualMap φ ∈ MM R p q := by
  intro φ hφ
  have : MM R p q ≤ (MM R p q).comap (pre1 R Z).dualMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨P, y⟩, rfl⟩
    show (pre1 R Z).dualMap (evalB R P y) ∈ MM R p q
    rw [dualMap_evalB]
    exact evalB_mem R _ _
  exact this hφ

def MMact : Mat p q →ₗ[ℂ] Module.End ℂ (MM R p q) where
  toFun Z := (pre1 R Z).dualMap.restrict (dualMap_mem R Z)
  map_add' Z W := by
    ext φ b
    simp [LinearMap.restrict_apply, LinearMap.dualMap_apply, invariantFockPairingPrecompAction_add]
  map_smul' c Z := by
    ext φ b
    simp [LinearMap.restrict_apply, LinearMap.dualMap_apply, invariantFockPairingPrecompAction_smul]

@[simp] theorem MMact_coe (Z : Mat p q) (φ : MM R p q) (b : invSub p q R) :
    ((MMact R Z φ : MM R p q) : Module.Dual ℂ (invSub p q R)) b = (φ : Module.Dual ℂ _) (pre1 R Z b) := rfl

def Ly (y : R.HK.V) : Pol p q r s →ₗ[ℂ] MM R p q where
  toFun P := ⟨evalB R P y, evalB_mem R P y⟩
  map_add' _ _ := by apply Subtype.ext; ext b; simp [evalB]
  map_smul' _ _ := by apply Subtype.ext; ext b; simp [evalB]

theorem MMact_Ly (Z : Mat p q) (y : R.HK.V) (P : Pol p q r s) :
    MMact R Z (Ly R y P) = Ly R y (fockAct1 p q r s Z P) := by
  apply Subtype.ext; ext b; rfl

theorem lie_MMact : IsLieAct (MMact R (p := p) (q := q)) := by
  intro Z W
  ext φ b
  rw [MMact_coe, invariantFockPairingPrecompAction_commutator]
  simp

theorem kfin_MMact (v : MM R p q) :
    ∃ W : Submodule ℂ (MM R p q), FiniteDimensional ℂ W ∧ v ∈ W ∧ KStable (MMact R) W := by
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨P, y⟩, rfl⟩ := hx
    obtain ⟨W₀, hfin, hP, hK⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
    refine ⟨W₀.map (Ly R y), inferInstance, ⟨P, hP, rfl⟩, ?_⟩
    rintro Z hZ _ ⟨P', hP', rfl⟩
    exact ⟨_, hK Z hZ P' hP', (MMact_Ly R Z y P').symm⟩
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun Z _ w hw => by
      rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨W₁, f₁, m₁, k₁⟩ := ihx
    obtain ⟨W₂, f₂, m₂, k₂⟩ := ihy
    refine ⟨W₁ ⊔ W₂, inferInstance, ?_, ?_⟩
    · exact Submodule.add_mem_sup m₁ m₂
    · intro Z hZ w hw
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (k₁ Z hZ a ha) (k₂ Z hZ c hc)
  | smul c x hx ih =>
    obtain ⟨W₁, f₁, m₁, k₁⟩ := ih
    exact ⟨W₁, f₁, W₁.smul_mem c m₁, k₁⟩

theorem Ly_wt (y : R.HK.V) (μ : Ix p q → ℚ) :
    (wtSub (fockAct1 p q r s) μ).map (Ly R y) ≤ wtSub (MMact R) μ := by
  rintro _ ⟨P, hP, rfl⟩
  simp only [SetLike.mem_coe, wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hP ⊢
  intro a
  have := hP a
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at this ⊢
  rw [MMact_Ly, ← map_smul, ← map_sub, this, map_zero]

theorem wts_MMact (v : MM R p q) : v ∈ ⨆ μ : Ix p q → ℚ, wtSub (MMact R) μ := by
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨P, y⟩, rfl⟩ := hx
    have hP := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2
    have h1 : Ly R y P ∈ (⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ).map (Ly R y) :=
      ⟨P, hP, rfl⟩
    rw [Submodule.map_iSup] at h1
    exact (iSup_mono fun μ => Ly_wt R y μ) h1
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => exact Submodule.smul_mem _ c ih

def MMgk (p q : ℕ) : GKMod p q where
  V := MM R p q
  act := MMact R
  lie := lie_MMact R
  kfin := kfin_MMact R
  wts := wts_MMact R

def BB : Pol p q r s →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] MM R p q :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => Ly R y P)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)
    (fun _ _ _ => by apply Subtype.ext; ext b; simp [Ly, evalB])
    (fun _ _ _ => by apply Subtype.ext; ext b; simp [Ly, evalB])

@[simp] theorem BB_apply (P : Pol p q r s) (y : R.HK.V) : BB R P y = Ly R y P := rfl

theorem eq_zero_of_noIntw (hadm : AdmGK R.HK)
    (hno : ∀ (M : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M.V R.HK.V),
      (∀ Z, f ∘ₗ fockAct1 p q r s Z = TensorProduct.map (M.act Z) LinearMap.id ∘ₗ f) →
      (∀ Y, f ∘ₗ fockAct2 p q r s Y = TensorProduct.map LinearMap.id (R.HK.act Y) ∘ₗ f) → f = 0)
    (b : Pairing p q R) (hb : IsInvPairing R b) : b = 0 := by
  have hinv : ∀ Z ∈ upq r s, ∀ (P : Pol p q r s) (y : R.HK.V),
      BB R (fockAct2 p q r s Z P) y + BB R P (R.HK.act Z y) = 0 := by
    intro Z hZ P y
    apply Subtype.ext; ext c
    have hc : IsInvPairing R c.1 := c.2
    simpa [Ly, evalB] using hc Z hZ P y
  obtain ⟨f, h2, hB, hc⟩ :=
    GlobalTheory.InvPairingTensor.exists_tensor_map p q r s T₂ R hadm (MM R p q) (BB R) hinv
  have h1 : ∀ Z, f ∘ₗ fockAct1 p q r s Z = TensorProduct.map (MMact R Z) LinearMap.id ∘ₗ f :=
    fun Z => hc _ _ fun P y => by simp [MMact_Ly]
  have hf : f = 0 := hno (MMgk R p q) f h1 h2
  refine LinearMap.ext fun P => LinearMap.ext fun y => ?_
  have h := hB P y
  rw [hf] at h
  simp only [LinearMap.zero_apply, map_zero, BB_apply] at h
  have h' := congrArg (fun φ : MM R p q => (φ : Module.Dual ℂ (invSub p q R)) ⟨b, hb⟩) h
  simpa [Ly, evalB] using h'

theorem eq_zero_of_noIntw' {T₀ : GrpData (p * r + q * s) (p * s + q * r)} {T₁ : GrpData p q}
    (F : FockData T₀ T₁ T₂) (hadm : AdmGK R.HK)
    (hno : ∀ (M : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M.V R.HK.V),
      IsIntw F M R.HK f → f = 0)
    (b : Pairing p q R) (hb : IsInvPairing R b) : b = 0 :=
  eq_zero_of_noIntw R hadm (fun M f h1 h2 => hno M f ⟨h1, h2⟩) b hb




end GlobalTheory.NoInvPairing
