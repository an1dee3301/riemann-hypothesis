module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds 

namespace GlobalTheory.ColRows

theorem isLattice_comap_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W]
    [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (e : W ≃ₗ[K] V) (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (N.comap ((e : W →ₗ[K] V).restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective ((e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.injective ?_
    rw [Submodule.map_comap_eq_of_surjective
      (f := (e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.surjective]
    exact hN.fg
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli


end GlobalTheory.ColRows
