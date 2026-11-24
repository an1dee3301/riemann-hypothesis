module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
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
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor

noncomputable section

namespace GlobalTheory.ThetaOrth

variable {D : D7}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    (starRingEnd ℂ) (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := GlobalTheory.SplitScalar.symplO_smul S T (N : AE D) x y
  rw [map_natCast] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) :
    symplO S T x (-y) = -symplO S T x y := by
  simp only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem isHalf_nsmul {m n : ℕ} {b : AE D} {y : Mx D m n} (hy : IsHalf b y) (N : ℕ) : IsHalf b (N • y) := by
  intro i j
  have e : (N • y) i j = N • y i j := rfl
  rw [e, nsmul_eq_mul, mul_left_comm, hy i j]

theorem isHalf_neg {m n : ℕ} {b : AE D} {y : Mx D m n} (hy : IsHalf b y) : IsHalf b (-y) := by
  intro i j
  have e : (-y) i j = -y i j := rfl
  rw [e, mul_neg, hy i j]

theorem isHalf_add {m n : ℕ} {b : AE D} {x y : Mx D m n} (hx : IsHalf b x) (hy : IsHalf b y) : IsHalf b (x + y) := by
  intro i j
  have e : (x + y) i j = x i j + y i j := rfl
  rw [e, mul_add, hx i j, hy i j]

theorem nsmul_add_neg {A : Type} [AddCommGroup A] (N k : ℕ) (t u v : A) (h : N • t = u + (N * k) • v) :
    N • (t + k • (-v)) = u := by
  rw [smul_add, h, smul_neg, mul_smul, smul_neg, add_neg_cancel_right]

theorem nsmul_add_mul {A : Type} [AddCommGroup A] (N k : ℕ) (t v : A) :
    N • (t + k • v) = N • t + (N * k) • v := by
  rw [smul_add, mul_smul]

theorem nsmul_inj {m n : ℕ} {N : ℕ} (hN : 0 < N) {x y : Mx D m n} (h : N • x = N • y) : x = y := by
  have hu : IsUnit (N : AE D) := by
    have h1 : IsUnit (N : D.host.E) := (Nat.cast_ne_zero.2 hN.ne').isUnit
    simpa only [map_natCast] using h1.map (incA D)
  refine Matrix.ext fun i j => ?_
  have e : N • x i j = N • y i j := congrFun (congrFun h i) j
  rw [nsmul_eq_mul, nsmul_eq_mul] at e
  exact hu.mul_left_cancel e

def charSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : AE D) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {p | ∃ y : WO S T, IsHalf b y ∧ p = fun t => ψ (symplO S T t y)}


open Classical in
theorem exists_char_of_wave {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {a : AE D} {Λ : AddSubgroup (WO S T)} (N : ℕ)
    {Ψ : WO S T → ℂ}
    (hΨ : Ψ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧
      Ψ = fun t => ψ (symplO S T t y) * halfInd a Λ (t + x)}) :
    ∃ q ∈ charSpan ψ S T (cA D a), ∀ t : WO S T, IsHalf a t → N • t ∈ Λ → Ψ (N • t) = q t := by
  induction hΨ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨x, y, hx, hy, rfl⟩ := h
    by_cases hxΛ : x ∈ Λ
    · refine ⟨fun t => ψ (symplO S T t (N • y)), Submodule.subset_span ⟨N • y, isHalf_nsmul hy N, rfl⟩, fun t ht htΛ => ?_⟩
      have h1 : halfInd a Λ (N • t + x) = 1 :=
        if_pos ⟨Λ.add_mem htΛ hxΛ, isHalf_add (isHalf_nsmul ht N) hx⟩
      show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = _
      rw [h1, mul_one, symplO_nsmul]
    · refine ⟨0, Submodule.zero_mem _, fun t ht htΛ => ?_⟩
      have h1 : halfInd a Λ (N • t + x) = 0 := if_neg fun h => hxΛ (by
        have := Λ.sub_mem h.1 htΛ
        rwa [add_sub_cancel_left] at this)
      show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = 0
      rw [h1, mul_zero]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ _ => rfl⟩
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    obtain ⟨q₁, m₁, e₁⟩ := h₁
    obtain ⟨q₂, m₂, e₂⟩ := h₂
    exact ⟨q₁ + q₂, Submodule.add_mem _ m₁ m₂, fun t ht hΛ => by
      rw [Pi.add_apply, Pi.add_apply, e₁ t ht hΛ, e₂ t ht hΛ]⟩
  | smul c Ψ _ h =>
    obtain ⟨q, m, e⟩ := h
    exact ⟨c • q, Submodule.smul_mem _ c m, fun t ht hΛ => by
      rw [Pi.smul_apply, Pi.smul_apply, e t ht hΛ]⟩



end GlobalTheory.ThetaOrth
