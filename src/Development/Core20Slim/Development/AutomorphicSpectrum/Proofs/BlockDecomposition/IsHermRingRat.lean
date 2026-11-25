module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

section Abstract

variable {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R)
  {V : Type} [AddCommGroup V] [Module R V]

structure IsHermRing : Prop where
  invol : ∀ a, c (c a) = a
  conj_mem : ∀ a ∈ 𝔬, c a ∈ 𝔬
  nontrivial : Nontrivial R
  artinian : IsArtinianRing R
  noeth : IsNoetherianRing 𝔬
  two : IsUnit (2 : R)
  denom : ∀ a : R, ∃ s ∈ 𝔬, IsUnit s ∧ s * a ∈ 𝔬
  principal : ∀ I : Submodule 𝔬 R, I.FG → (∃ u ∈ I, IsUnit u) → ∃ u : R, IsUnit u ∧ I = Submodule.span 𝔬 {u}

structure IsHerm (h : V → V → R) : Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (a : R) (x y : V), h x (a • y) = a * h x y
  symm : ∀ x y, h y x = c (h x y)

structure IsPerfect (h : V → V → R) : Prop where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0
  repr : ∀ f : V →ₗ[R] R, ∃ x, ∀ y, h x y = f y

def IsLat (L : Submodule 𝔬 V) : Prop :=
  L.FG ∧ Submodule.span R (L : Set V) = ⊤

def IsEvenInt (h : V → V → R) (L : Submodule 𝔬 V) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, h x y ∈ 𝔬) ∧ ∀ x ∈ L, ∃ a ∈ 𝔬, h x x = a + c a

def IsMaxEven (h : V → V → R) (L : Submodule 𝔬 V) : Prop :=
  IsLat 𝔬 L ∧ IsEvenInt c 𝔬 h L ∧ ∀ L' : Submodule 𝔬 V, IsEvenInt c 𝔬 h L' → L ≤ L' → L' ≤ L

structure IsFrame {r : ℕ} (h : V → V → R) (x y : Fin r → V) : Prop where
  xx : ∀ i j, h (x i) (x j) = 0
  yy : ∀ i j, h (y i) (y j) = 0
  xy : ∀ i j, h (x i) (y j) = if i = j then 1 else 0

def IsIsomOnto (h : V → V → R) (p : V ≃ₗ[R] V) (L L' : Submodule 𝔬 V) : Prop :=
  (∀ x y, h (p x) (p y) = h x y) ∧ ∀ z, z ∈ L ↔ p z ∈ L'

def HasBase : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    (∀ x y, h x x = 0 → h x y ≠ 1) → ∀ L L' : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → IsMaxEven c 𝔬 h L' →
      ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L'

def FlagTransitive : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    ∀ (r : ℕ) (x y : Fin r → V), IsFrame h x y → ∀ L L' : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → IsMaxEven c 𝔬 h L' →
      ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L' ∧
        ∀ j, p (x j) ∈ Submodule.span R (x '' {i | i ≤ j})

def IsAdapted {r : ℕ} (h : V → V → R) (x y : Fin r → V) (L : Submodule 𝔬 V) : Prop :=
  ∀ z, z ∈ L ↔ (∀ i, h (x i) z ∈ 𝔬) ∧ (∀ i, h (y i) z ∈ 𝔬) ∧
    z - ∑ i, h (y i) z • x i - ∑ i, h (x i) z • y i ∈ L

end Abstract

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def colV (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin r) E) (i : Fin r) : Fin n → Fv F v ⊗[F] E :=
  fun a => inclR (F := F) (Fv F v) (X a i)

def stabLat {v : HeightOneSpectrum (𝓞 F)} (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)) :
    Subgroup (GLoc σ J v) where
  carrier := {g | ∀ y, y ∈ Λ ↔ (matHom _ σ J g).1 *ᵥ y ∈ Λ}
  one_mem' := fun y => by simp
  mul_mem' := fun {a b} ha hb y => by
    rw [hb y, ha, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  inv_mem' := fun {a} ha y => by
    rw [ha ((matHom _ σ J a⁻¹).1 *ᵥ y), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    simp

theorem mem_stabLat {v : HeightOneSpectrum (𝓞 F)} {Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)}
    {g : GLoc σ J v} : g ∈ stabLat σ J Λ ↔ ∀ y, y ∈ Λ ↔ (matHom _ σ J g).1 *ᵥ y ∈ Λ := Iff.rfl

def leviMat (A : Type) [CommRing A] [Algebra F A] (X Y : Matrix (Fin n) (Fin r) E)
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E) :=
  let Xa := X.map (inclR (F := F) A)
  let Ya := Y.map (inclR (F := F) A)
  let Xd := (cT (σ : E →+* E) X * J).map (inclR (F := F) A)
  let Yd := (cT (σ : E →+* E) Y * J).map (inclR (F := F) A)
  let P := 1 - Xa * Yd - Ya * Xd
  Xa * diagonal (fun i => (Yd * M * Xa) i i) * Yd + Ya * diagonal (fun i => (Xd * M * Ya) i i) * Xd + P * M * P

end Place

end GlobalTheory.CompanionTheory.KFin

end
