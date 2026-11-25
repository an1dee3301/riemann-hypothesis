module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicImage
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Rational
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RationalCyclotomic
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Subtype.Order
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Directed
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Norm.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IntermediateField IdeleGroup

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield RationalSymbol _root_.GroundTheory.Global.Cyclotomic

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem exists_le_sup_rootsOfUnityField (K L : FiniteSubfield) (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) :
    ∃ m : ℕ+, L.1 ≤ K.1 ⊔ rootsOfUnityField m := by
  obtain ⟨α, hα⟩ : ∃ α : L.1,
      @IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α} = ⊤ := by
    have e : IntermediateField.algebra' L.1 = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    rw [e]
    exact Field.exists_primitive_element ℚ L.1
  have hdir : Directed (· ≤ ·) fun m : ℕ+ ↦ K.1 ⊔ rootsOfUnityField m := fun m n ↦
    ⟨m * n, sup_le_sup_left (rootsOfUnityField_le_mul m n) _,
      sup_le_sup_left (by rw [mul_comm]; exact rootsOfUnityField_le_mul n m) _⟩
  have hmem : (α : ℚ̄) ∈ ⨆ m : ℕ+, K.1 ⊔ rootsOfUnityField m := by
    rw [← sup_iSup, ← maxCyclotomic_eq_iSup]
    exact hL α.2
  rw [← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at hmem
  obtain ⟨m, hm⟩ := hmem
  refine ⟨m, fun y hy ↦ ?_⟩
  have hy' : y ∈ (@IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α}).map
      L.1.val :=
    ⟨⟨y, hy⟩, by rw [hα]; trivial, rfl⟩
  rw [adjoin_map, Set.image_singleton] at hy'
  exact adjoin_simple_le_iff.2 hm hy'

theorem agreesOn_cycRestrict (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) : AgreesOn m g (cycRestrict g) :=
  fun z hz ↦ (coe_cycRestrict_apply g ⟨z, rootsOfUnityField_le_maxCyclotomic m hz⟩).symm

variable (K L : FiniteSubfield) [Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

instance isGalois_of_fact : IsGalois K.1 L.1 :=
  isGalois_of_normal


omit [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] in
theorem isScalarTower_of_le (E : FiniteSubfield) [Fact (K ≤ E)] [Fact (L ≤ E)] :
    IsScalarTower K.1 L.1 E.1 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem ideleSymbol_diagonal_eq_one_of_le_sup (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) (a : K.1ˣ) :
    ideleSymbol K.1 L.1 (diagonal K.1 a) = 1 := by
  obtain ⟨m, hm⟩ := exists_le_sup_rootsOfUnityField K L hL
  have : Fact (L ≤ compositum K (layer m)) := ⟨hm⟩
  have := isScalarTower_of_le K L (compositum K (layer m))
  have h1 : ((1 : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal (rootsOfUnityField m) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 (diagonal K.1 a)) := by
    rw [ideleNorm_diagonal, range_diagonal_le_ker_layer m ⟨_, rfl⟩]
    exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) (rootsOfUnityField m))
  have hE := restrictHom_eq_ideleSymbol K (layer m) 1 (diagonal K.1 a) h1
  rw [map_one] at hE
  rw [← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]
  exact map_one (AlgEquiv.restrictNormalHom (F := K.1) (K₁ := (compositum K (layer m)).1) L.1)

theorem restrictHom_eq_ideleSymbol_of_le_sup (hL : L.1 ≤ K.1 ⊔ maxCyclotomic)
    (g : K.1.fixingSubgroup) (x : IdeleGroup K.1)
    (hg : cycRestrict (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = cycSymbol K (IdeleClassGroup.mk K.1 x)) :
    restrictHom (E := L) g = ideleSymbol K.1 L.1 x := by
  obtain ⟨m, hm⟩ := exists_le_sup_rootsOfUnityField K L hL
  have : Fact (L ≤ compositum K (layer m)) := ⟨hm⟩
  have := isScalarTower_of_le K L (compositum K (layer m))
  have h1 : ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)).restrictNormal (rootsOfUnityField m) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 x) := by
    have h := agreesOn_cycRestrict m (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)
    rw [hg, agreesOn_cycSymbol_iff, layerSymbol_mk] at h
    exact h
  have hE := restrictHom_eq_ideleSymbol K (layer m) g x h1
  rw [← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]
  refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
  exact (congrArg Subtype.val
    (AlgEquiv.restrictNormal_commutes (restrictHom (E := compositum K (layer m)) g) L.1 y)).symm

end CyclotomicSymbol

end

end GroundTheory.Global
