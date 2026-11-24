module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.thetaLift_translate_of_kernel_fixed : ∀ {G H S Sinf Ds Dt : Type} [Group G] [Group H]
    [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (It : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt),
    _root_.Formalism.IndefR.Lift.IsIo ν 𝓕 th pt It CCs CCt io →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (It φ v) = 0) → u = 0) →
    ∀ (k : G) (k' : H) (a a' : ℂ), (∀ g h φ, a * th (g * k) (h * k') (pt φ) = a' * th g h (pt φ)) →
    (∀ (F : CCs) φ v g, ∫ h in 𝓕, th g (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') ∂ν =
      ∫ h in 𝓕, th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h ∂ν) →
    ∀ (F F' : CCs) (u : CCt), (∀ v h, (F' : Ds →ₗ[ℂ] (H → ℂ)) v h = a' * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) →
    (∀ v g, (u : Dt →ₗ[ℂ] (G → ℂ)) v g = a * ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) v (g * k)) →
    io F' = u := by
  intro G H S Sinf Ds Dt _ _ _ _ _ _ _ _ _ ν 𝓕 th pt It CCs CCt io hio hker k k' a a' hth hinv
    F F' u hF' hu
  refine sub_eq_zero.mp (hker (io F' - u) fun φ v => ?_)
  funext g
  simp only [Submodule.coe_sub, LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply]
  rw [sub_eq_zero, ← hio.eq F' φ v g, hu, ← hio.eq F φ v (g * k)]
  unfold _root_.Formalism.IndefR.Lift.liftInt
  rw [← hinv F φ v (g * k), ← integral_const_mul]
  congr 1
  funext h
  rw [hF', show a * (th (g * k) (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) =
    (a * th (g * k) (h * k') (pt φ)) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') from
    (_root_.mul_assoc _ _ _).symm, hth]
  ring

end GlobalTheory
