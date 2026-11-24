module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace Bl.EqIdOfFixed

private lemma ne_id_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h
  obtain ⟨-, hc, -, hs⟩ := h
  by_contra hne0
  have hne : ∀ z : E, σ z = z := fun z => by_contra fun hz => hne0 ⟨z, hz⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := hc
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext z
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have := hs τ z
  rw [hne z] at this
  exact this.symm

private lemma eq_id_of_fix {F E : Type} [Field F] [Field E] [Algebra F E]
    (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) {x : E} (hx : σ x = x)
    (hno : ∀ t : F, algebraMap F E t ≠ x) (y : E) : σ y = y := by
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hno (-(s / t))
      have h1 : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : x = t⁻¹ • -(s • (1 : E)) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hc : Fintype.card (Fin 2) = Module.finrank F E := by simp [hd]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have heq : σ.toLinearMap = (LinearMap.id : E →ₗ[F] E) := by
    apply b.ext
    intro i
    fin_cases i
    · simp [b]
    · simp [b, hx]
  exact LinearMap.congr_fun heq y

theorem goal1 :
  ∀ {F E : Type} [inst : Field.{0} F] [inst_1 : NumberField.{0} F] [inst_2 : Field.{0} E] [inst_3 : NumberField.{0} E]
  [inst_4 : Algebra.{0, 0} F E] {σ : AlgHom.{0, 0, 0} F E E},
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
    ∀ {x : E},
      Eq.{1} (DFunLike.coe.{1, 1, 1} σ x) x →
        Exists.{1} fun (t : F) ↦ Eq.{1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} F E) t) x := by
  intro F E _ _ _ _ _ σ h x hx
  by_contra hno0
  have hno : ∀ t : F, algebraMap F E t ≠ x := fun t ht => hno0 ⟨t, ht⟩
  obtain ⟨y, hy⟩ := ne_id_of_cm σ h
  have h' := h
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h'
  exact hy (eq_id_of_fix h'.2.2.1 σ hx hno y)

end Bl.EqIdOfFixed
