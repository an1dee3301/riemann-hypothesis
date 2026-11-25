module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.UnitaryGroupScheme
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)

section Coordinates

variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]

noncomputable def matrixCoords : Matrix ι ι (R ⊗[F] E) ≃ (ι × ι × κ → R) where
  toFun g p := (Algebra.TensorProduct.basis R b).repr (g p.1 p.2.1) p.2.2
  invFun x i j := (Algebra.TensorProduct.basis R b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k => x (i, j, k))
  left_inv g := by
    ext i j
    simp
  right_inv x := by
    funext ⟨i, j, k⟩
    simp



variable {R}





end Coordinates

end GroundTheory.Automorphic
