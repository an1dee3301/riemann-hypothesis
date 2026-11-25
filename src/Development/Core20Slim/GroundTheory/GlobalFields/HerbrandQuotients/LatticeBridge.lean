module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.Lattice
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.Permutation
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Finiteness.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open MulAction
open scoped TensorProduct

variable {G : Type*} [Group G] [Fintype G]

theorem cyclicHerbrand_eq_cycHerbrand {M : Type*} [AddCommGroup M] (ρ : Representation ℤ G M)
    (σ : G) : cyclicHerbrand ρ σ = cycHerbrand ρ σ :=
  rfl

theorem cycHerbrand_trivial_int (σ : G) :
    cycHerbrand (Representation.trivial ℤ G ℤ) σ = Fintype.card G :=
  cyclicHerbrand_trivial_int σ

theorem cycHerbrand_eq_of_real_equiv {M M' : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    [Module.Free ℤ M] [AddCommGroup M'] [Module.Finite ℤ M'] [Module.Free ℤ M']
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G)
    (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ :=
  cyclicHerbrand_eq_of_real_equiv ρ ρ' σ e he

end GroundTheory.Global
