module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDualsStatement
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem isDefGram_map {E K : Type} [Field E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) (f : E →+* K)
    (hf : ∀ x, star (f x) = f (cE x)) {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ φ : E →+* ℂ, (A.map φ).PosDef) : IsDefGram (A.map f) := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun (hA (σ.comp f)).isHermitian.eq a) b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h ⊢
    rw [hf]
    apply σ.injective
    have h2 := hc (σ.comp f) (A b a)
    simp only [RingHom.comp_apply] at h h2
    rw [h2]
    exact h
  · intro a b ψ
    simp only [Matrix.map_apply]
    rw [hf]
    exact hc (ψ.comp f) _
  · intro φ
    rw [Matrix.map_map]
    exact hA (φ.comp f)

theorem map_inv_of_isUnit_det {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hA : IsUnit A.det) : (A.map f)⁻¹ = A⁻¹.map f := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA]
  simp

theorem isUnit_det_map {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) : IsUnit (A.map f).det ↔ IsUnit A.det := by
  have : (A.map f).det = f A.det := by rw [RingHom.map_det]; rfl
  rw [this, isUnit_iff_ne_zero, isUnit_iff_ne_zero, map_ne_zero]

private theorem selfDualE_full {E : Type} [Field E] [NumberField E] {n : ℕ}
    (cE : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSelfDualE cE J L) :
    Submodule.IsFullLattice E L := by
  classical
  haveI : Submodule.IsLattice E L := hL.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hL.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin n → E) → E := fun x => Formalism.UG.hform cE J x y
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) s f
  have ha0 : (algebraMap (𝓞 E) E a) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 E) (Fin n → E) := {
    carrier := {x | ∃ b : 𝓞 E, (b : E) = (algebraMap (𝓞 E) E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f, Formalism.UG.hform]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : E) + c = _
      rw [hb, hc]
      simp [f, Formalism.UG.hform, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom cE c * b, ?_⟩
      simp only [map_mul, hb, f, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def,
        RingOfIntegers.mapRingHom_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring }
  have hsP : (s : Set (Fin n → E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 E) E a) • y ∈ L := by
    apply (hL.2 _).2
    intro x hx
    obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
    refine ⟨b, ?_⟩
    change (b : E) = _
    rw [hb]
    simp only [f, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 E) E a) • y ∈ Submodule.span E (L : Set (Fin n → E)) :=
    Submodule.subset_span hy
  have := (Submodule.span E (L : Set (Fin n → E))).smul_mem (algebraMap (𝓞 E) E a)⁻¹ hy'
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem defGram_selfDual_of_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  intro E K _ _ _ _ _ cE hc ι emb hemb n J hJ τ
  obtain ⟨φ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hdet : IsUnit J.det :=
    (isUnit_det_map φ₀ J).1 ((Matrix.isUnit_iff_isUnit_det _).1 (hJ φ₀).isUnit)
  have h1 : IsDefGram (gramK emb J τ) := isDefGram_map cE hc (emb τ) (hemb τ) J hJ
  have hdK : IsUnit (gramK emb J τ).det := (isUnit_det_map (emb τ) J).2 hdet
  refine ⟨h1, ?_, ?_⟩
  · have e : gramKd emb J τ = ((J⁻¹)ᵀ).map (emb τ) := by
      unfold gramKd
      rw [map_inv_of_isUnit_det _ _ hdet, Matrix.transpose_map]
    rw [e]
    refine isDefGram_map cE hc (emb τ) (hemb τ) _ fun φ => ?_
    rw [Matrix.transpose_map, ← map_inv_of_isUnit_det _ _ hdet]
    exact (hJ φ).inv.transpose
  · intro L hL
    have hfull := selfDualE_full cE J L hL
    have hl : Submodule.IsFullLattice K (tauLat emb τ L) := GlobalTheory.T.lattice_extension_along_field_embedding_duals.1 E K ι n emb τ L hfull
    have hd : hdualFr (gramK emb J τ) (tauLat emb τ L) = tauLat emb τ L :=
      GlobalTheory.T.lattice_extension_along_field_embedding_duals.2.1 E K ι n emb cE τ (hemb τ) J L L hdet hfull hL.2
    refine ⟨⟨hl.toIsLattice, hd⟩, (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K n _ _ hdK hl).1.toIsLattice, ?_⟩
    have h := GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.2 K n _ _ h1.1 hdK hl
    rw [hd] at h
    exact h

end GlobalTheory.TestLat
