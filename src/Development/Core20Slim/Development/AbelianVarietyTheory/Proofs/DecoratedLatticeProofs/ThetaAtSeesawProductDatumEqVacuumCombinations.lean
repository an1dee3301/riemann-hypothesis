module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.VecProd

section Gen
variable {D : D7}

theorem isHalf_add_iff {a b : AE D} (hab : b * a = 0) {m n : ℕ} (t : Mx D m n) :
    IsHalf (a + b) t ↔ IsHalf b (t - t.map (fun x => a * x)) := by
  constructor
  · intro h i j
    have h1 := h i j
    simp only [Matrix.sub_apply, Matrix.map_apply]
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]
    linear_combination h1
  · intro h i j
    have h1 := h i j
    simp only [Matrix.sub_apply, Matrix.map_apply] at h1
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero] at h1
    linear_combination h1

theorem isHalf_zero_iff {m n : ℕ} (t : Mx D m n) : IsHalf (0 : AE D) t ↔ t = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := h i j
    rw [zero_mul] at h1
    simpa using h1.symm
  · rintro rfl i j
    simp

theorem half_add_of_right {a b : AE D} (hab : b * a = 0) {m n : ℕ} {w : Mx D m n} (hw : IsHalf a w) :
    IsHalf (b + a) w := by
  intro i j
  have h : b * w i j = 0 := by rw [← hw i j, ← mul_assoc, hab, zero_mul]
  rw [add_mul, h, zero_add, hw i j]

theorem half_conj_add_of_right {a b : AE D} (hab : b * a = 0) {m n : ℕ} {y : Mx D m n} (hy : IsHalf (cA D a) y) :
    IsHalf (cA D (b + a)) y := by
  intro i j
  have h : cA D b * y i j = 0 := by rw [← hy i j, ← mul_assoc, ← map_mul, hab, map_zero, zero_mul]
  rw [map_add (f := _), add_mul, h, zero_add, hy i j]

theorem symplO_sub {S T : HSp D} (x w y : WO S T) :
    symplO S T (x - w) y = symplO S T x y - symplO S T w y := by
  have h : hO S T (x - w) y = hO S T x y - hO S T w y := by
    simp only [hO, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  unfold symplO
  rw [h, mul_sub, map_sub]

theorem hO_zero' {S T : HSp D} {a b : AE D} (hab : b * a = 0) {w y : WO S T} (hw : IsHalf a w)
    (hy : IsHalf (cA D b) y) : hO S T w y = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have h1 : cA D (y c j) = b * cA D (y c j) := by
    conv_lhs => rw [← hy c j, map_mul, Formalism.L2.Theta.cA_cA]
  rw [h1, ← hw d i]
  linear_combination (incA D (S.gram⁻¹ i j) * cA D (y c j) * incA D (T.gram c d) * w d i) * hab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']







end Gen

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Fam
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}







end Fam

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Core
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}




end Core

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Fin2
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}






end Fin2


end GlobalTheory.VecProd

end
