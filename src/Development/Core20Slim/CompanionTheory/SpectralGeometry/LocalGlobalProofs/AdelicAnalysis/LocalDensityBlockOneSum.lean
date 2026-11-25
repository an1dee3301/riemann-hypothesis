module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalUnitsContinuousSquareRootStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneFiberMeasureBlockExtensionStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductSupportStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegralStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductInvarianceStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductNormalizationStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforwardStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDensityStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductRecursionStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fibre_family_near_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J), Measurable s → (∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y) → (∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C') → ∃ B : Set (HermR R σ (n + 1)), IsOpen B ∧ hermOf R σ _ hT' ∈ B ∧ (∀ S ∈ B, IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1)) (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B)) (coordHerm R σ b lam (n + 1)) B fib ∧ fib (hermOf R σ _ hT') = c ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdet hT' R _ _ _ _ _ hR d b lam hlam m₁ m' hm₁ hm' c hc s hs hsec hcpt
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hJ t ht
  obtain ⟨tu, htu⟩ : IsUnit (algebraMap F R t) := (isUnit_iff_ne_zero.mpr ht).map (algebraMap F R)
  obtain ⟨B₀, a, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.local_units_continuous_square_root R hR tu
  rw [htu] at h2 h5 h6
  obtain ⟨κ₁, cm, k1, k2, k3, k4, k5, k6⟩ := GlobalTheory.T.coordK_map_mul_eq_smul_continuous_modulus F E σ hCM (M + 1) _ hJ' t ht R hR d b lam hlam m₁ hm₁
  have D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm :=
    { hCM := hCM, hJ := hJ, ht := ht, hR := hR, hlam := hlam, hm₁ := hm₁, hm' := hm', hs := hs, hsec := hsec,
      hcpt := hcpt, hB₀ := h1, htB := h2, hac := h3, hoff := h4, hsq := h5, ha1 := h6, hκc := k1, hκ1 := k2,
      hscale := k3, hcmc := k4, hmod := k5 }
  have V := GlobalTheory.T.gram_fiber_cons_at_block_one_eq_map_prod F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  refine ⟨Bset R σ t a B₀, (GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2.2.2.2, V.1,
    GlobalTheory.T.isUnit_det_of_mem_Bset' F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D, fibS σ J t m₁ m' s B₀ a κ₁ cm,
    ⟨GlobalTheory.T.gram_fiber_cons_concentrated_on_fiber F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D, ?_, ?_⟩, ?_⟩
  · intro φ hφ
    exact (GlobalTheory.T.setLIntegral_Uset_coordW_eq_Mid F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).trans
      (GlobalTheory.T.gram_fiber_cons_iterated_lintegral_eq_Mid F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).symm
  · intro φ hc hs' _
    exact GlobalTheory.T.gram_fiber_cons_integrable_and_continuousOn_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hc hs'
  · rw [V.2, k6 c hc]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
