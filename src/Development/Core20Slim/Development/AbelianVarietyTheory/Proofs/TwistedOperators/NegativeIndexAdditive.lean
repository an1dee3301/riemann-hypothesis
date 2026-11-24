module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Formalism.LocalRingCardinality.DataSpaces
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.SumSig

section Change
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem gram_family (S : HSpace E) {ι : Type} [Fintype ι] (v : ι → S.V) :
    (Matrix.of fun k l => S.hT (v k) (v l)) =
      (Matrix.of fun i k => S.frame.repr (v k) i)ᴴ * S.gram * Matrix.of fun i k => S.frame.repr (v k) i := by
  ext k l
  have hk := S.frame.sum_repr (v k)
  have hl := S.frame.sum_repr (v l)
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram]
  conv_lhs => rw [← hk, ← hl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    Finset.sum_mul, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Change

end GlobalTheory.SumSig
