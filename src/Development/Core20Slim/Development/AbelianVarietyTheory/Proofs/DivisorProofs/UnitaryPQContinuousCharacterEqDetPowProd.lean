module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupContinuousCharEqDetZpowStatement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.UpqChar


theorem char_unitary {p : ℕ} (f : Matrix.unitaryGroup (Fin p) ℂ → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hn : ∀ a, ‖f a‖ = 1) (hc : Continuous f) :
    ∃ x : ℤ, ∀ a, f a = (Matrix.det (a : Matrix (Fin p) (Fin p) ℂ)) ^ x := by
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have hne : f 1 ≠ 0 := fun h0 => by simpa [h0] using hn 1
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)
  have hmem : ∀ a, f a ∈ Submonoid.unitSphere ℂ := fun a => mem_sphere_zero_iff_norm.2 (hn a)
  let c : Matrix.unitaryGroup (Fin p) ℂ →* Circle :=
    { toFun := fun a => ⟨f a, hmem a⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcont : Continuous c := Continuous.subtype_mk hc hmem
  obtain ⟨m, hm⟩ := GlobalTheory.T.unitaryGroup_continuous_char_eq_det_zpow p c hcont
  exact ⟨m, fun a => hm a⟩



end GlobalTheory.UpqChar
