module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.SInteger

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain

section GroupLemma

variable {G C : Type*} [Group G] [Group C]

theorem index_map_mul_relIndex_ker {f : G →* C} (hf : Function.Surjective f) (W : Subgroup G)
    [W.Normal] : (W.map f).index * W.relIndex f.ker = W.index := by
  rw [Subgroup.index_map, f.range_eq_top_of_surjective hf, Subgroup.index_top, mul_one,
    ← Subgroup.relIndex_sup_left, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

end GroupLemma

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem index_comap_sUnitsToSIdeles (W : Subgroup (sIdeles S)) :
    (W.comap (sUnitsToSIdeles S)).index = W.relIndex (sIdelesToIdeleClassGroup S).ker := by
  rw [Subgroup.index_comap, range_sUnitsToSIdeles]

theorem index_map_mul_index_comap (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (W : Subgroup (sIdeles S)) :
    (W.map (sIdelesToIdeleClassGroup S)).index * (W.comap (sUnitsToSIdeles S)).index =
      W.index := by
  rw [index_comap_sUnitsToSIdeles]
  exact index_map_mul_relIndex_ker ((sIdelesToIdeleClassGroup_surjective_iff S).2 h) W

end IdeleGroup

end

end GroundTheory.Global
