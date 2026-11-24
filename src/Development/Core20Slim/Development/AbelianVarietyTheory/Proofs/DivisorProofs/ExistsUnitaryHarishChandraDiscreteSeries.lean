module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.DiscreteSeriesUnitary

def unitaryModule {p q : ℕ} {T : GrpData p q} (D : DSRep T) : UGKMod p q where
  M := D.HK
  ip := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => inner ℂ (D.ι x) (D.ι y))
    (fun x y z => by simp only [map_add (f := _), inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])
    (fun x y z => by simp only [map_add (f := _), inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  herm x y := inner_conj_symm (D.ι y) (D.ι x)
  pos x hx := by
    have h : D.ι x ≠ 0 := fun h => hx (D.ι_inj (h.trans (map_zero D.ι).symm))
    exact re_inner_self_pos (𝕜 := ℂ).2 h
  adj Z x y := GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T D.U D.HK D.ι D.der Z x y

theorem exists_unitary : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T),
    ∃ M : UGKMod p q, M.M = D.HK :=
  fun _ _ _ D => ⟨unitaryModule D, rfl⟩

end GlobalTheory.DiscreteSeriesUnitary

end
