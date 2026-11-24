module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AnisotropicRestrict
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AnisotropicUnitaryRes
public import Development.Core20Slim.GroundTheory.AutomorphicForms.UnitaryGroupScheme
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Topology

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "𝒩" => Fintype.card (ι × κ)

theorem continuous_coords : Continuous (coords b R) :=
  (tensorCoordsHomeomorph R b).continuous

theorem continuous_coords_symm : Continuous (coords b R).symm :=
  (tensorCoordsHomeomorph R b).symm.continuous

theorem continuous_resHom :
    Continuous (resHom (ι := ι) b R : Matrix ι ι (R ⊗[K] E) → Matrix (Fin 𝒩) (Fin 𝒩) R) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  show Continuous fun M : Matrix ι ι (R ⊗[K] E) => coords b R
    (baseBasis b R ((Fintype.equivFin (ι × κ)).symm p).2 *
      M ((Fintype.equivFin (ι × κ)).symm p).1 ((Fintype.equivFin (ι × κ)).symm q).1)
        ((Fintype.equivFin (ι × κ)).symm q).2
  exact (continuous_apply _).comp ((continuous_coords b R).comp
    (continuous_const.mul (continuous_id.matrix_elem _ _)))

theorem continuous_trHom : Continuous (trHom (ι := ι) b R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_resHom b R).comp Units.continuous_coe_inv.matrix_transpose
  · exact (continuous_resHom b R).comp Units.continuous_val.matrix_transpose

def readoff (A : Matrix (Fin 𝒩) (Fin 𝒩) R) : Matrix ι ι (R ⊗[K] E) := fun i j =>
  (coords b R).symm fun l => ∑ k, coords b R 1 k *
    A (Fintype.equivFin (ι × κ) (i, k)) (Fintype.equivFin (ι × κ) (j, l))

theorem readoff_resHom (M : Matrix ι ι (R ⊗[K] E)) : readoff b R (resHom b R M) = M := by
  ext i j
  apply (coords b R).injective
  rw [readoff, LinearEquiv.apply_symm_apply]
  funext l
  have h := congrFun (coords_mul b R 1 (M i j)) l
  rw [one_mul] at h
  rw [h]
  simp only [vecMul, dotProduct, resHom_apply, Equiv.symm_apply_apply, blockHom_apply]

theorem continuous_readoff : Continuous (readoff (ι := ι) b R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_coords_symm b R).comp (continuous_pi fun l => ?_)
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_id.matrix_elem _ _)

end Topology

section Star

variable {R : Type*} [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

def cstar (X : Matrix ι ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E) := (X.map (conjBase K E R))ᵀ

theorem cstar_mul (X Y : Matrix ι ι (R ⊗[K] E)) : cstar (X * Y) = cstar Y * cstar X := by
  simp only [cstar, Matrix.map_mul, transpose_mul]

theorem cstar_one : cstar (1 : Matrix ι ι (R ⊗[K] E)) = 1 := by
  simp [cstar]

theorem map_baseMap_mul (f : R →ₐ[K] R') (X Y : Matrix ι ι (R ⊗[K] E)) :
    (X * Y).map (baseMap f) = X.map (baseMap f) * Y.map (baseMap f) :=
  Matrix.map_mul (f := (baseMap f : R ⊗[K] E →ₐ[K] R' ⊗[K] E).toRingHom)

theorem cstar_baseMap (f : R →ₐ[K] R') (X : Matrix ι ι (R ⊗[K] E)) :
    cstar (X.map (baseMap f)) = (cstar X).map (baseMap f) := by
  have commute (z : R ⊗[K] E) :
      conjBase K E R' (tensorMap E f z) = tensorMap E f (conjBase K E R z) := by
    induction z using TensorProduct.inductionOn with
    | tmul r e => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  ext i j
  simp only [cstar, transpose_apply, Matrix.map_apply, baseMap_eq_tensorMap, commute]

theorem baseMatrix_baseMap (f : R →ₐ[K] R') :
    (baseMatrix K H R).map (baseMap f) = baseMatrix K H R' := by
  ext i j
  simp only [baseMatrix, Matrix.map_apply, baseMap_eq_tensorMap, tensorMap,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one,
    AlgHom.id_apply]

theorem cstar_mul_baseMatrix_map (f : R →ₐ[K] R') (X : Matrix ι ι (R ⊗[K] E)) :
    (cstar X * baseMatrix K H R * X).map (baseMap f) =
      cstar (X.map (baseMap f)) * baseMatrix K H R' * X.map (baseMap f) := by
  rw [map_baseMap_mul, map_baseMap_mul, cstar_baseMap, baseMatrix_baseMap]

end Star

section Main

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable [NumberField K]

theorem baseMap_ofId_injective :
    Function.Injective (baseMap (Algebra.ofId K 𝔸[K]) : K ⊗[K] E → 𝔸[K] ⊗[K] E) := by
  let b := Module.finBasis K E
  intro z z' h
  apply (coords b K).injective
  funext k
  have h1 := congrFun (congrArg (coords b 𝔸[K]) h) k
  rw [coords_baseMap, coords_baseMap] at h1
  exact AdeleRing.algebraMap_injective (𝓞 K) K h1

theorem mem_unitaryPoints_of_diagGL {m : GL ι (K ⊗[K] E)}
    (hm : diagGL (Algebra.ofId K 𝔸[K]) m ∈ unitaryPoints K E H 𝔸[K]) : m ∈ unitaryPoints K E H K := by
  have hm' : cstar ((diagGL (Algebra.ofId K 𝔸[K]) m : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι _) *
      baseMatrix K H 𝔸[K] * (diagGL (Algebra.ofId K 𝔸[K]) m : Matrix ι ι _) =
      baseMatrix K H 𝔸[K] := hm
  show cstar (m : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * m = baseMatrix K H K
  rw [diagGL_val, ← cstar_mul_baseMatrix_map, ← baseMatrix_baseMap H (Algebra.ofId K 𝔸[K])] at hm'
  exact Matrix.map_injective baseMap_ofId_injective hm'

end Main

end Anisotropic

end

end GroundTheory.Automorphic
