module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn.HalfOff

variable {D : D7} {S T : HSp D}

theorem smul_apply' (b : AE D) (t : WO S T) (i j) : (b • t) i j = b * t i j := by
  rw [Matrix.smul_apply, smul_eq_mul]


theorem half_smul {b : AE D} (hb : b * b = b) (t : WO S T) : IsHalf b (b • t) := fun i j => by
  rw [smul_apply', ← mul_assoc, hb]



theorem tens_vac {a b : AE D} (hab : a * b = 0) (hb : b * b = b) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens b ((1 : ℂ) • halfInd a Λ) (halfInd b Λ) = (1 : ℂ) • halfInd (a + b) Λ := by
  classical
  funext t
  simp only [one_smul, tens_apply]
  set M : WO S T := b • t with hMdef
  have hM : IsHalf b M := half_smul hb t
  have key : ((t - M ∈ Λ ∧ IsHalf a (t - M)) ∧ M ∈ Λ) ↔ (t ∈ Λ ∧ IsHalf (a + b) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 h3, fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, smul_apply'] at h
      linear_combination h + t i j * hab
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λ := hΛ t h1
      refine ⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, smul_apply']
      linear_combination h2 i j - t i j * hab
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (a + b) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos ⟨h3, hM⟩, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λ
    · rw [if_pos (show M ∈ Λ ∧ IsHalf b M from ⟨h3, hM⟩), mul_one,
        if_neg (show ¬(t - M ∈ Λ ∧ IsHalf a (t - M)) from fun h => hR (key.1 ⟨h, h3⟩))]
    · rw [if_neg (show ¬(M ∈ Λ ∧ IsHalf b M) from fun h => h3 h.1), mul_zero]

end GlobalTheory.FinPl.PutIn.HalfOff



end
