module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowstLemmas
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.ColumnInclusionRenaming

theorem fockS_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockS (rename e f) (rename e g) = fockS f g := by
  classical
  unfold fockS
  rw [support_rename_of_injective he, Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  congr 2
  unfold mfact
  rw [Finsupp.mapDomain_support_of_injective he, Finset.prod_image (fun _ _ _ _ h => he h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective he]




end GlobalTheory.Proof.ColumnInclusionRenaming
