module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisRest
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew

theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.HermitianEigenvalueInequality.main
  | exact _root_.GlobalTheory.HermitianEigenvalueInequality.main
  | (apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianEigenvalueInequality.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianEigenvalueInequality.main ..)

theorem isLattice_lowLat : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  intro E _ _ n n₁ L ι hL hι
  have hfg : L.FG := Submodule.IsLattice.fg (self := hL)
  refine ⟨?_, ?_⟩
  · let f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E)
    have hf : Function.Injective f := hι
    have hle : (lowLat ι L).map f ≤ L := Submodule.map_comap_le f L
    have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hfg
    have hm : ((lowLat ι L).map f).FG := (isNoetherian_submodule.mp hN) _ hle
    exact Submodule.fg_of_fg_map_injective f hf hm
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.PlaneSkew
