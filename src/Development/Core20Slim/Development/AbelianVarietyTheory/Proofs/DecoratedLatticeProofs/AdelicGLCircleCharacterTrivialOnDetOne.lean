module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvectionsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmFieldStatement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
