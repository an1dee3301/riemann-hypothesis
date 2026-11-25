module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace ComplementForm

theorem conj_apply (h : HermitianForm F E W) (x y : W) :
    conjHom F E (h.toSesq x y) = h.toSesq y x :=
  LinearMap.isSymm_def.1 h.isSymm x y

theorem apply_w_v {h : HermitianForm F E W} {v w : W} (hp : IsHyperbolicPair h v w) :
    h.toSesq w v = 1 := by
  rw [← conj_apply h v w, hp.2.2, map_one]

def proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict (hypComplement h v w)
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w) fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, smul_eq_mul, hp.1, hp.2.1, hp.2.2, apply_w_v hp]
      constructor <;> ring

theorem proj_apply (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    (proj h v w hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem eq_add_proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    x = h.toSesq w x • v + (proj h v w hp x : W) + h.toSesq v x • w := by
  rw [proj_apply]; abel

theorem proj_of_mem (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w)
    (x : hypComplement h v w) : proj h v w hp x = x := by
  obtain ⟨h1, h2⟩ := mem_hypComplement.1 x.2
  ext
  rw [proj_apply, h1, h2, zero_smul, zero_smul, sub_zero, sub_zero]

def restr (h : HermitianForm F E W) (v w : W) :
    hypComplement h v w →ₛₗ[conjHom F E] hypComplement h v w →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E) (fun x y => h.toSesq x y)
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul])
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _)])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply])

theorem restr_apply (h : HermitianForm F E W) (v w : W) (x y : hypComplement h v w) :
    restr h v w x y = h.toSesq x y := rfl

def form (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    HermitianForm F E (hypComplement h v w) where
  toSesq := restr h v w
  isSymm := LinearMap.isSymm_def.2 fun x y => conj_apply h x y
  nonsingular := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨h1, h2⟩ := mem_hypComplement.1 a.2
      have hav : h.toSesq a v = 0 := by rw [← conj_apply, h1, map_zero]
      have haw : h.toSesq a w = 0 := by rw [← conj_apply, h2, map_zero]
      have hall : h.toSesq (a : W) = 0 := by
        ext y
        have hy : h.toSesq (a : W) (proj h v w hp y) = 0 := by
          rw [← restr_apply, ha, LinearMap.zero_apply]
        rw [eq_add_proj h v w hp y, map_add (f := _), map_add (f := _), map_smul, map_smul, hav, haw, hy,
          LinearMap.zero_apply]
        simp
      have : (a : W) = 0 := h.nonsingular.1 (hall.trans (map_zero _).symm)
      exact Subtype.ext this
    · intro φ
      obtain ⟨y, hy⟩ := h.nonsingular.2 (φ ∘ₗ proj h v w hp)
      have hpv : proj h v w hp v = 0 := by
        ext; rw [proj_apply, hp.1, apply_w_v hp, one_smul, zero_smul]; simp
      have hpw : proj h v w hp w = 0 := by
        ext; rw [proj_apply, hp.2.1, hp.2.2, one_smul, zero_smul]; simp
      have hyv : h.toSesq y v = 0 := by
        rw [hy, LinearMap.comp_apply, hpv, map_zero]
      have hyw : h.toSesq y w = 0 := by
        rw [hy, LinearMap.comp_apply, hpw, map_zero]
      have hmem : y ∈ hypComplement h v w := by
        rw [mem_hypComplement, ← conj_apply h y v, ← conj_apply h y w, hyv, hyw, map_zero]
        exact ⟨rfl, rfl⟩
      refine ⟨⟨y, hmem⟩, ?_⟩
      ext z
      rw [restr_apply, hy, LinearMap.comp_apply, proj_of_mem]

end ComplementForm

theorem ComplementForm.proof (h : HermitianForm F E W) : ComplementForm.Statement h :=
  fun v w hp => ⟨ComplementForm.form h v w hp, fun _ _ => rfl⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
