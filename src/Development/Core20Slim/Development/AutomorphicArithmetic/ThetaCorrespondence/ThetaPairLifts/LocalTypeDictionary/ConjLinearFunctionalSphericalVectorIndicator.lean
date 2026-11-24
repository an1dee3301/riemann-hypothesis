module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSplitPlaceComponentsDualStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LinearFunctionalSphericalVectorNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.WithVal

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix
noncomputable section
namespace GlobalTheory.SplitBarVac
theorem conjLinearFunctional_sphericalVector_indicator : FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ b₁ : GL (Fin n) (Fv F v), (PsiUnr B.ψ v → b₁ = b) ∧ ∃ ι, M.IsLinBar B.ψ t b₁ c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  have hcm : IsCMExt F E σ := hPair.base.cm
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have htt : (t.comp σ).comp σ = t := AlgHom.ext fun x => by simp [hσσ]
  have hJX : IsHermND σ X.Jᵀ := ⟨fun i j => by simp [Matrix.transpose_apply, hPair.herm.herm],
    by rw [Matrix.det_transpose]; exact HermSelfDualLoc.det_ne_zero_of_isHerm σ B hPair.herm⟩
  have hL := HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hPair.base hPair.herm v
  have hb2 := hb.dual hcm hJX hL
  obtain ⟨z, c₂, hz1, hc2v, hc2⟩ := T.skewHermitianLattice_splitPlace_components_dual F E σ B d W r' s' hPair.base hPair.skew v t c hc
  have hc3 : IsSplitBasis (t.comp σ) W.L (-c₂) := fun u => by
    have := hc2 (-u)
    simp only [Pi.neg_apply, neg_mem_iff, Matrix.mulVec_neg] at this
    simpa [Units.val_neg, Matrix.neg_mulVec, Matrix.mulVec_neg] using this
  refine ⟨Units.map (Matrix.scalar (Fin n) : Fv F v →+* Matrix (Fin n) (Fin n) (Fv F v)).toMonoidHom z * b,
    fun hu => by simp [hz1 hu], ?_⟩
  obtain ⟨ι, hι, hvac⟩ := T.linearFunctional_sphericalVector_ne_zero hP F E σ B n d X W M χX χW om r s r' s' hPair v (t.comp σ) _ _ hb2 hc3
  refine ⟨ι, ?_, hvac⟩
  unfold Model.IsLinW at hι
  rw [htt] at hι
  unfold Model.IsLinBar
  convert hι using 1
  have e1 : ((dualConj 1 (splitGram hJX t * b))⁻¹).1 = b.1ᵀ * X.J.map t := by
    rw [← map_inv, dualConj_val]
    simp [Matrix.transpose_mul, Matrix.transpose_map]
  have e2 : ((-c₂)⁻¹).1 = -((z : Fv F v) • (c.1ᵀ * W.J.map t)) := by
    first
    | (rw [← hc2v]; simp)
    | (rw [← hc2v, Units.neg_inv]; rfl)
    | (rw [← hc2v]; exact congrArg Units.val (neg_inv c₂))
  ext Y i j
  rw [e1, e2]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.transpose_mul, Matrix.scalar_apply,
    Matrix.transpose_neg, Matrix.transpose_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.diagonal_transpose, Matrix.mul_assoc, neg_neg]
  simp [Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, Matrix.smul_mul]
end GlobalTheory.SplitBarVac
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_sphericalVector_indicator_value : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ b₁ : GL (Fin n) (Fv F v), (PsiUnr B.ψ v → b₁ = b) ∧ ∃ ι, M.IsLinBar B.ψ t b₁ c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @_root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator | exact _root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator | (intros; apply _root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator <;> assumption)
end
