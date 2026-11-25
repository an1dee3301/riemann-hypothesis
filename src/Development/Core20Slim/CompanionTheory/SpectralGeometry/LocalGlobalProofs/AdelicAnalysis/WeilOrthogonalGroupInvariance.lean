module

public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Units
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.OrthMeas

theorem chiB_mulVec_mulVec {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    (ψ : AddChar R ℂ) (B g : Matrix ι ι R) (hg : gᵀ * B * g = B) (x y : ι → R) :
    chiB ψ B (g *ᵥ x) (g *ᵥ y) = chiB ψ B x y := by
  have h : (g *ᵥ x) ⬝ᵥ (B *ᵥ (g *ᵥ y)) = x ⬝ᵥ (B *ᵥ y) := by
    conv_rhs => rw [← hg]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x gᵀ,
      Matrix.vecMul_transpose]
  simp only [chiB, h]

def mulVecEquiv {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Matrix ι ι R) (hdet : IsUnit g.det) : (ι → R) ≃+ (ι → R) where
  toFun x := g *ᵥ x
  invFun x := g⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet]
  map_add' := Matrix.mulVec_add g

theorem perp_image {V : Type} (χ : V → V → ℂ) (e : V ≃ V)
    (hχ : ∀ x y, χ (e x) (e y) = χ x y) (L : Set V) :
    perp χ (e '' L) = e '' perp χ L := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, fun x hx => ?_, e.apply_symm_apply y⟩
    have := hy (e x) ⟨x, hx, rfl⟩
    rwa [← e.apply_symm_apply y, hχ] at this
  · rintro ⟨z, hz, rfl⟩ x ⟨w, hw, rfl⟩
    rw [hχ]
    exact hz w hw

theorem map_eq_self {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V) (hD : NADual V χ μ) (e : V ≃+ V) (he : Continuous e)
    (hes : Continuous e.symm) (hχ : ∀ x y, χ (e x) (e y) = χ x y) :
    Measure.map e μ = μ := by
  obtain ⟨hTG, hT2, hLC, hSC, hBS, hHaar, -, hEx, -, -, -, -, hPerp⟩ := hD
  haveI := hTG
  haveI := hT2
  haveI := hLC
  haveI := hSC
  haveI := hBS
  haveI := hHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.map e = c • μ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map e) μ⟩
  let t : V ≃ₜ V := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  have key : ∀ A : Set V, IsOpen A → μ A = c * μ (e '' A) := by
    intro A hA
    have hm : MeasurableSet (e '' A) := (t.isOpenMap A hA).measurableSet
    have h1 : (μ.map e) (e '' A) = (c • μ) (e '' A) := by rw [hc]
    rw [Measure.map_apply he.measurable hm, Set.preimage_image_eq _ e.injective,
      Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    exact h1
  obtain ⟨L, hLc, hLo, -⟩ := hEx 0
  have hset : ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) = e '' (L : Set V) := by
    ext x; simp
  have hL'c : IsCompact ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) := by
    rw [hset]; exact hLc.image he
  have hL'o : IsOpen ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) := by
    rw [hset]; exact t.isOpenMap _ hLo
  obtain ⟨-, hPo, -, hP⟩ := hPerp L hLc hLo
  obtain ⟨-, -, -, hP'⟩ := hPerp _ hL'c hL'o
  rw [hset, show perp χ (e '' (L : Set V)) = e '' perp χ (L : Set V) from
    perp_image χ e.toEquiv hχ _] at hP'
  have hcc : ((c : ℝ≥0∞)) * c = 1 := by
    rw [key _ hLo, key _ hPo] at hP
    calc ((c : ℝ≥0∞)) * c = (c : ℝ≥0∞) * c * (μ (e '' (L : Set V)) * μ (e '' perp χ (L : Set V))) := by
          rw [hP', mul_one]
      _ = 1 := by rw [← hP]; ring
  have hc1 : c = 1 := by
    have h2 : c * c = 1 := by exact_mod_cast hcc
    have h3 : c ^ 2 = 1 := by rw [sq]; exact h2
    exact (pow_eq_one_iff.1 h3).resolve_right two_ne_zero
  rw [hc, hc1, one_smul]

theorem orth_meas : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)),
    NAQuad ψ h B μ → ∀ g : Matrix ι ι R, IsUnit g.det → gᵀ * B * g = B →
      Measure.map (fun x => g *ᵥ x) μ = μ ∧ ∀ φ : (ι → R) → ℂ, SB φ →
        SB (fun x => φ (g *ᵥ x)) ∧
          ∀ y, fou (chiB ψ B) μ (fun x => φ (g *ᵥ x)) y = fou (chiB ψ B) μ φ (g *ᵥ y) := by
  intro R _ _ _ ι _ _ ψ h B μ hQ g hdet hg
  obtain ⟨hTR, -, -, -, -, hD⟩ := hQ
  haveI := hTR
  have hBS : BorelSpace (ι → R) := hD.2.2.2.2.1
  have he : Continuous (mulVecEquiv g hdet) :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hes : Continuous (mulVecEquiv g hdet).symm :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hχ : ∀ x y, chiB ψ B (mulVecEquiv g hdet x) (mulVecEquiv g hdet y) = chiB ψ B x y :=
    chiB_mulVec_mulVec ψ B g hg
  have hmap : Measure.map (fun x => g *ᵥ x) μ = μ :=
    map_eq_self (chiB ψ B) μ hD (mulVecEquiv g hdet) he hes hχ
  let t : (ι → R) ≃ₜ (ι → R) :=
    { toEquiv := (mulVecEquiv g hdet).toEquiv, continuous_toFun := he, continuous_invFun := hes }
  refine ⟨hmap, fun φ hφ => ⟨⟨hφ.1.comp_continuous he, hφ.2.comp_homeomorph t⟩, fun y => ?_⟩⟩
  have hI := t.measurableEmbedding.integral_map (μ := μ) (fun x => φ x * chiB ψ B x (g *ᵥ y))
  have ht : (⇑t : (ι → R) → (ι → R)) = fun x => g *ᵥ x := rfl
  rw [ht, hmap] at hI
  simp only [fou]
  rw [hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [chiB_mulVec_mulVec ψ B g hg]

end GlobalTheory.CompanionTheory.SW.Core.OrthMeas
