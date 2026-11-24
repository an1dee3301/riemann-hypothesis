module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Prod
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK



variable (F : Type) [Field F] [NumberField F]


def trP (κ : Type) [Fintype κ] : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun _ _ _ => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])
    (fun _ _ _ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun _ _ _ => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])

theorem mixedTracePairing_apply {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    trP F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl


variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n}
  {W : Spc F E d} {W₁ : Spc F E d₁}


end GlobalTheory.ArchSch
