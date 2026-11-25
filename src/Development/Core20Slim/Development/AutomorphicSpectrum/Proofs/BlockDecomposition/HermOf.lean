module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
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
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (σ : E →ₐ[F] E) (n : ℕ) : Submodule F (Matrix (Fin n) (Fin n) E) where
  carrier := {c | ∀ a b, σ (c b a) = c a b}
  add_mem' := by
    intro c d hc hd a b
    simp [map_add (f := _), hc a b, hd a b]
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro t c hc a b
    simp [hc a b]

def hermIn (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (n : ℕ) :
    hermE σ n →+ HermR R σ n where
  toFun c := hermOf R σ c.1 c.2
  map_zero' := by
    apply Subtype.ext
    ext a b
    simp [hermOf]
  map_add' := by
    intro c d
    apply Subtype.ext
    ext a b
    simp [hermOf]

variable [NumberField E]

def hermO (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (hermE σ n) where
  carrier := {c | ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b}
  add_mem' := by
    intro c d hc hd a b
    obtain ⟨o, ho⟩ := hc a b
    obtain ⟨p, hp⟩ := hd a b
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun a b => ⟨0, by simp⟩
  neg_mem' := by
    intro c hc a b
    obtain ⟨o, ho⟩ := hc a b
    exact ⟨-o, by simp [ho]⟩

def Kc {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : AddSubgroup (Fin n → 𝓞 E) where
  carrier := {y | ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i}
  add_mem' := by
    intro y z hy hz i
    obtain ⟨o, ho⟩ := hy i
    obtain ⟨p, hp⟩ := hz i
    refine ⟨o + p, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((y + z) j)) =
        (fun j => algebraMap (𝓞 E) E (y j)) + fun j => algebraMap (𝓞 E) E (z j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_add, Pi.add_apply, ← ho, ← hp, map_add (f := _)]
  zero_mem' := fun i => ⟨0, by
    have h0 : (fun _ : Fin n => (0 : E)) = 0 := rfl
    simp [h0, Matrix.mulVec_zero]⟩
  neg_mem' := by
    intro y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨-o, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((-y) j)) = -fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_neg, Pi.neg_apply, ← ho, map_neg]

def delta {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : ℕ := (Kc c).index

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
