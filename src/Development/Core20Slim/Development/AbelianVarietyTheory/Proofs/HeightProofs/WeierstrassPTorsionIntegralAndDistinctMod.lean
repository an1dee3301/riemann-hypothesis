module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.TorsionIntegral

theorem dbl (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) (h2 : w + w ∉ L.lattice) :
    L.weierstrassP (w + w) * (4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) =
      (L.weierstrassP w ^ 2 + L.g₂ / 4) ^ 2 + 2 * L.g₃ * L.weierstrassP w := by
  obtain ⟨e, he⟩ := GlobalTheory.weierstrass_uniformisation.2.1 L
  obtain ⟨h1, e1⟩ := he w hw
  obtain ⟨h2', e2⟩ := he _ h2
  have hy : L.derivWeierstrassP w ≠ 0 := fun h => h2 ((GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).1 h)
  have hne : L.derivWeierstrassP w / 2 ≠
      (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP w) (L.derivWeierstrassP w / 2) := by
    simp [GlobalTheory.latticeCurve]
    intro h; apply hy; linear_combination h
  rw [QuotientAddGroup.mk_add, map_add (f := _), e1, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne] at e2
  have e3 := (WeierstrassCurve.Affine.Point.some.inj e2).1
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hne] at e3
  simp [GlobalTheory.latticeCurve] at e3
  have hsq := L.derivWeierstrassP_sq w hw
  rw [← e3, ← hsq]
  field_simp
  rw [hsq]
  ring


theorem sum_prod (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hne : L.weierstrassP z ≠ L.weierstrassP w) :
    (L.weierstrassP (z + w) + L.weierstrassP (z - w)) * (L.weierstrassP z - L.weierstrassP w) ^ 2 =
      2 * L.weierstrassP z * L.weierstrassP w * (L.weierstrassP z + L.weierstrassP w)
        - L.g₂ / 2 * (L.weierstrassP z + L.weierstrassP w) - L.g₃ ∧
    L.weierstrassP (z + w) * L.weierstrassP (z - w) * (L.weierstrassP z - L.weierstrassP w) ^ 2 =
      (L.weierstrassP z * L.weierstrassP w + L.g₂ / 4) ^ 2
        + L.g₃ * (L.weierstrassP z + L.weierstrassP w) := by
  have h3 := (GlobalTheory.weierstrassP_add L hz hw hne).1
  have hw' : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  have h4 := (GlobalTheory.weierstrassP_add L hz hw' (by rwa [L.weierstrassP_neg])).1
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg, ← sub_eq_add_neg] at h4
  have s1 := L.derivWeierstrassP_sq z hz
  have s2 := L.derivWeierstrassP_sq w hw
  have hd : L.weierstrassP z - L.weierstrassP w ≠ 0 := sub_ne_zero.2 hne
  generalize L.weierstrassP (z + w) = x3 at *
  generalize L.weierstrassP (z - w) = x4 at *
  generalize L.weierstrassP z = x1 at *
  generalize L.weierstrassP w = x2 at *
  generalize L.derivWeierstrassP z = y1 at *
  generalize L.derivWeierstrassP w = y2 at *
  have a3 : x3 * (x1 - x2) ^ 2 = (y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2) - y1 * y2 / 2 := by
    rw [h3]; field_simp; ring
  have a4 : x4 * (x1 - x2) ^ 2 = (y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2) + y1 * y2 / 2 := by
    rw [h4]; field_simp; ring
  constructor
  · linear_combination a3 + a4 + s1 / 2 + s2 / 2
  · apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    have : (x3 * (x1 - x2) ^ 2) * (x4 * (x1 - x2) ^ 2) =
        ((y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2)) ^ 2 - y1 ^ 2 * y2 ^ 2 / 4 := by
      rw [a3, a4]; ring
    rw [s1, s2] at this
    linear_combination this








end GlobalTheory.TorsionIntegral
