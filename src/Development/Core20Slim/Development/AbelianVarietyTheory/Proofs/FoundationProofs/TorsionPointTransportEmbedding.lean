module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GlobalTheory

open WeierstrassCurve

theorem nsmul_some_map_eq_zero_iff {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    (i : F →+* K) (W : WeierstrassCurve F) (x y : F) (N : ℕ)
    (h₀ : W.toAffine.Nonsingular x y) (h : (W.map i).toAffine.Nonsingular (i x) (i y)) :
    N • (Affine.Point.some (i x) (i y) h) = 0 ↔ N • (Affine.Point.some x y h₀) = 0 := by
  letI : Algebra F K := i.toAlgebra
  let φ : W.toAffine.Point →+ (W.map i).toAffine.Point :=
    Affine.Point.map (W' := W.toAffine) (Algebra.ofId F K)
  have hφ : Function.Injective φ := Affine.Point.map_injective (W' := W.toAffine) (Algebra.ofId F K)
  have e : φ (Affine.Point.some x y h₀) = Affine.Point.some (i x) (i y) h := rfl
  rw [← e, ← map_nsmul, map_eq_zero_iff φ hφ]

theorem torsion_point_transport_embedding :
    ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [DecidableEq K] [DecidableEq K'] (i : F →+* K) (j : F →+* K') (A B x y : F) (N : ℕ) (h : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K).toAffine.Nonsingular (i x) (i y)), N • (WeierstrassCurve.Affine.Point.some (i x) (i y) h) = 0 → ∃ h' : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K').toAffine.Nonsingular (j x) (j y), N • (WeierstrassCurve.Affine.Point.some (j x) (j y) h') = 0 := by
  intro F K K' _ _ _ _ _ i j A B x y N
  classical
  let W : WeierstrassCurve F := ⟨0, 0, 0, A, B⟩
  have ei : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K) = W.map i := by
    ext <;> simp [W, WeierstrassCurve.map]
  have ej : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K') = W.map j := by
    ext <;> simp [W, WeierstrassCurve.map]
  rw [ei, ej]
  intro h hN
  have h₀ : W.toAffine.Nonsingular x y := (W.toAffine.map_nonsingular i.injective x y).mp h
  have h' : (W.map j).toAffine.Nonsingular (j x) (j y) :=
    (W.toAffine.map_nonsingular j.injective x y).mpr h₀
  exact ⟨h', (nsmul_some_map_eq_zero_iff j W x y N h₀ h').mpr
    ((nsmul_some_map_eq_zero_iff i W x y N h₀ h).mp hN)⟩

end GlobalTheory
