module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapPiScale
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.UnitScale

theorem map_pi_scale {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, α i → α i) (hg : ∀ i, Measurable (g i))
    (c : ι → ℝ≥0∞) (hc0 : ∀ i, c i ≠ 0) (hct : ∀ i, c i ≠ ⊤)
    (h : ∀ i, (μ i).map (g i) = c i • μ i) :
    (Measure.pi μ).map (fun x i => g i (x i)) = (∏ i, c i) • Measure.pi μ :=
  _root_.UpperTheory.Reformulated.B.MapPiScale.map_pi_scale μ g hg c hc0 hct h

end GlobalTheory.CompanionTheory.AvgFree.UnitScale


open GlobalTheory.CompanionTheory.AvgFree.UnitScale in
theorem GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n M : ℕ) (l : Fin n) (D : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), MeasurableSet D → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) {X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) ∈ D} = ((θ : ℝ≥0∞) ^ M)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) D := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv s θ hθ n M l D hD
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := hlv.1
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hK
  set μ := GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv with hμ
  haveI : SigmaFinite μ := inferInstance
  let g : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun x => (s : Fv F v ⊗[F] E) * x
  have hgm : Measurable g := (continuous_const.mul continuous_id).measurable
  have hgs : Function.Surjective g := fun y =>
    ⟨((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * y, by simp [g]⟩
  have hθ0 : (θ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have h1 := hθ Set.univ
    rw [h0, zero_mul] at h1
    have h2 : (fun x => (s : Fv F v ⊗[F] E) * x) '' Set.univ = Set.univ := Set.image_univ_of_surjective hgs
    rw [h2] at h1
    exact (IsOpen.measure_pos μ isOpen_univ ⟨0, trivial⟩).ne' h1
  have hθt : (θ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hmap : μ.map g = (θ : ℝ≥0∞)⁻¹ • μ := by
    ext Y hY
    rw [Measure.map_apply hgm hY, Measure.smul_apply, smul_eq_mul]
    have h1 := hθ (g ⁻¹' Y)
    have h2 : (fun x => (s : Fv F v ⊗[F] E) * x) '' (g ⁻¹' Y) = Y := Set.image_preimage_eq Y hgs
    rw [h2] at h1
    rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hθ0 hθt, one_mul]

  have hvec : (Measure.pi fun _ : Fin M => μ).map (fun x i => g (x i)) =
      ((θ : ℝ≥0∞)⁻¹ ^ M) • Measure.pi fun _ : Fin M => μ := by
    have := GlobalTheory.CompanionTheory.AvgFree.UnitScale.map_pi_scale (fun _ : Fin M => μ) (fun _ => g) (fun _ => hgm) (fun _ => (θ : ℝ≥0∞)⁻¹)
      (fun _ => ENNReal.inv_ne_zero.2 hθt) (fun _ => ENNReal.inv_ne_top.2 hθ0) (fun _ => hmap)
    simpa using this
  have hvm : Measurable (fun (x : Fin M → Fv F v ⊗[F] E) i => g (x i)) :=
    Measurable.of_eval fun i => hgm.comp (measurable_pi_apply i)
  let gV : Fin n → (Fin M → Fv F v ⊗[F] E) → (Fin M → Fv F v ⊗[F] E) := fun a =>
    if a = l then (fun x i => g (x i)) else id
  let c : Fin n → ℝ≥0∞ := fun a => if a = l then (θ : ℝ≥0∞)⁻¹ ^ M else 1
  have hgV : ∀ a, Measurable (gV a) := fun a => by
    by_cases h : a = l
    · simpa [gV, h] using hvm
    · simpa [gV, h] using measurable_id
  have hc0 : ∀ a, c a ≠ 0 := fun a => by
    by_cases h : a = l
    · simpa [c, h, hθt] using fun _ => hθt
    · simp [c, h]
  have hct : ∀ a, c a ≠ ⊤ := fun a => by
    by_cases h : a = l
    · simpa [c, h] using ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hθ0)
    · simp [c, h]
  have hmapV : ∀ a, (Measure.pi fun _ : Fin M => μ).map (gV a) = c a • Measure.pi fun _ : Fin M => μ :=
    fun a => by
    by_cases h : a = l
    · simpa [gV, c, h] using hvec
    · simp [gV, c, h]
  have htup := GlobalTheory.CompanionTheory.AvgFree.UnitScale.map_pi_scale (fun _ : Fin n => Measure.pi fun _ : Fin M => μ) gV hgV c hc0 hct hmapV
  have hT : Measurable (fun (x : Fin n → Fin M → Fv F v ⊗[F] E) a => gV a (x a)) :=
    Measurable.of_eval fun a => (hgV a).comp (measurable_pi_apply a)
  have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E |
      GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : Fv F v ⊗[F] E)) ∈ D} =
      (fun (x : Fin n → Fin M → Fv F v ⊗[F] E) a => gV a (x a)) ⁻¹' D := by
    ext X
    have : GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : Fv F v ⊗[F] E)) = fun a => gV a (X a) := by
      funext a i
      by_cases h : a = l
      · subst h
        simp [GlobalTheory.CompanionTheory.SW.rmul, dMat, Matrix.diagonal_apply, gV, g, mul_comm]
      · simp [GlobalTheory.CompanionTheory.SW.rmul, dMat, Matrix.diagonal_apply, gV, h]
    simp [this]
  have hprod : (∏ a, c a) = ((θ : ℝ≥0∞) ^ M)⁻¹ := by
    simp [c, ENNReal.inv_pow]
  show (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => μ) _ = _ *
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => μ) D
  rw [hset, ← Measure.map_apply hT hD, htup, hprod, Measure.smul_apply, smul_eq_mul]
