module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsFibreFamilyTransport
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresScalingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresUniqueAeStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid
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
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibScale

theorem fib_rmul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * S * g) → ∀ a c : ℝ≥0, μ.map (fun X => rmul R X g) = a • μ → ν.map τ = c • ν → ∀ S, a • m (τ S) = c • (m S).map (fun X => rmul R X g) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g hg τ hτ a c hmu hnu S
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  obtain ⟨halg, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hg2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun X : Fin n → Fin M → R ⊗[F] E => rmul R X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := fun X => rmul R X g
      invFun := fun X => rmul R X g⁻¹
      left_inv := fun X => by simp only [hcomp, hg1, hone]
      right_inv := fun X => by simp only [hcomp, hg2, hone]
      continuous_toFun := hrc g
      continuous_invFun := hrc g⁻¹ }
  have hc1 : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    unfold cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 →
      cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h' = A := by
    intro h h' A hh
    have h1 : cT (sigR R σ) h' * cT (sigR R σ) h = 1 := by
      rw [← cT_mul, hh, hc1]
    calc cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h'
        = (cT (sigR R σ) h' * cT (sigR R σ) h) * A * (h * h') := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]
  let τ' : HermR R σ n → HermR R σ n := fun S =>
    ⟨cT (sigR R σ) g⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E), Continuous fun S : HermR R σ n =>
      cT (sigR R σ) h * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := τ
      invFun := τ'
      left_inv := fun S => Subtype.ext (by
        show cT (sigR R σ) g⁻¹ * ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹ = S
        rw [hτ]
        exact key _ _ _ hg1)
      right_inv := fun S => Subtype.ext (by
        rw [hτ]
        exact key _ _ _ hg2)
      continuous_toFun := by
        refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
        exact (hcj g).congr fun S => (hτ S).symm
      continuous_invFun := (hcj g⁻¹).subtype_mk _ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hdet : ∀ h A : Matrix (Fin n) (Fin n) (R ⊗[F] E), IsUnit h.det → IsUnit A.det →
      IsUnit (cT (sigR R σ) h * A * h).det := by
    intro h A hh hA
    have h1 : (cT (sigR R σ) h).det = sigR R σ h.det := by
      rw [RingHom.map_det]
      simp [cT, Matrix.det_transpose]
    rw [Matrix.det_mul, Matrix.det_mul, h1]
    exact ((hh.map (sigR R σ)).mul hA).mul hh
  have hBτ : τh '' B = B := by
    ext S'
    constructor
    · rintro ⟨S, hS, rfl⟩
      show IsUnit ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
      rw [hτ]
      exact hdet _ _ hg hS
    · intro hS'
      exact ⟨τh.symm S', hdet _ _ hgi hS', τh.apply_symm_apply _⟩
  have hU : G ⁻¹' B = {X | IsUnit (gramR R σ J X).det} := by
    ext X
    show IsUnit _ ↔ IsUnit _
    rw [hGe]
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (G ⁻¹' B) ν B m := by
    rw [hU]
    exact hm
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (rmul R X g) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((τ (G X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, hτ, ← hGe]
    exact halg X g
  have htr := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ ν (gramR R σ J) G Subtype.val
    Subtype.val_injective hGc hGe _ (gramR R σ J) G hGc hGe e τh hcomm B hBo m hfam
  rw [hBτ, hU] at htr
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have hnew : IsGramFib R σ J n (a • μ) (c • ν) (fun b => (m (τh.symm b)).map e) := htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := GlobalTheory.T.gram_fiber_measures_scaling F E σ hσ M J hJ R hR n μ ν m hμ hν hm a c ha0 hc0
  have huq := GlobalTheory.T.gram_fiber_measures_unique F E σ hσ M J hJ R hR n (a • μ) (c • ν) _ hμa hνc hres _ hnew (τ S)
  have hs : τh.symm (τ S) = S := τh.symm_apply_apply S
  simp only [hs] at huq
  have hfin : (m S).map (fun X => rmul R X g) = (a / c) • m (τ S) := huq.symm
  rw [hfin, smul_smul, mul_div_cancel₀ a hc0]

end GlobalTheory.CompanionTheory.SW.FibScale
