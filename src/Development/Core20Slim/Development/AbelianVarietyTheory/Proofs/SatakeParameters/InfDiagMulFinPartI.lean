module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

namespace GlobalTheory.UnUnitCmp.Val

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

def intFin (L : Type) [Field L] [NumberField L] : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers L}
  one_mem' := fun _ => one_mem _
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (intFin L ⧸ Ideal.span {(N : intFin L)}) := by
  let ι : 𝓞 L →+* intFin L :=
    ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap (𝓞 L) L)).codRestrict _
      fun x v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v x
  have : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 L)})
    (Ideal.span {(N : intFin L)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : intFin L)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).2 z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : FiniteAdeleRing (𝓞 L) L) - algebraMap L _ (x : L) = ((N : intFin L) : FiniteAdeleRing (𝓞 L) L) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp


theorem infDiag_mul_finPartI (k : Lˣ) : infDiag k * finPartI L (diagUnits L k) = diagUnits L k := by
  classical
  have h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem exists_pow_eq (x : Ideles L) (hx : IsFinIdele x) :
    ∃ h : ℕ, 0 < h ∧ ∃ (u : Ideles L) (k : Lˣ), IsFinIdele u ∧ u ∈ unitIdl L ∧ x ^ h * infDiag k = u * diagUnits L k := by
  have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨_, Nat.pos_of_ne_zero this.index_ne_zero, ?_⟩
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
  have hf : finPartI L x = x := Units.ext (Prod.ext (funext hx).symm rfl)
  refine ⟨finPartI L u, k, fun _ => rfl, hu, ?_⟩
  rw [← hf, ← map_pow, ← e, map_mul, mul_assoc, mul_comm _ (infDiag k), infDiag_mul_finPartI]

end GlobalTheory.UnUnitCmp.Val
