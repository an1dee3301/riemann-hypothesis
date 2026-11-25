module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord

theorem schurM_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hinv : ∀ y : R ⊗[F] E, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS := S.2 i.succ j.succ
  have ht : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, ht]
  rw [hS]
  ring

theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) ∧ ContinuousOn (fun S : HermR R σ (n + 1) => (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ IsOpen (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hTR, hLC, hSC, hT2, hAr, hRed, hUR, -⟩ := D.hR
  have hK := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨hKR, -, -, -, hsig, htr, -⟩ := hK
  have hinv := (GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R).2.2.2.1
  have hopenU := GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR

  have hs0 : Continuous (fun S : HermR R σ (n + 1) =>
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
    unfold s0
    have h1 : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) :=
      (continuous_apply_apply 0 0).comp continuous_subtype_val
    exact continuous_const.mul (htr.comp h1)
  have hA : IsOpen {S : HermR R σ (n + 1) |
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := D.hB₀.preimage hs0
  have ha : ContinuousOn (fun S : HermR R σ (n + 1) =>
      a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    D.hac.comp hs0.continuousOn (fun S hS => hS)

  have hleft : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    have : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [this]
    exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))
  have hc : ContinuousOn (fun S : HermR R σ (n + 1) =>
      cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) :=
      (continuous_apply_apply 0 j.succ).comp continuous_subtype_val
    have hu : ContinuousOn (fun S : HermR R σ (n + 1) =>
        ((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R)))
        {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
      (Units.continuous_val (M := R)).comp_continuousOn ha.inv
    have hfac : (fun S : HermR R σ (n + 1) =>
        cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j) =
        fun S : HermR R σ (n + 1) =>
        (((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) *
          ((1 : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) *
          (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      funext S
      simp [cvec, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hfac]
    exact ((hleft.comp_continuousOn hu).mul continuousOn_const).mul hent.continuousOn

  have hM : ContinuousOn (fun S : HermR R σ (n + 1) =>
      schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) :=
      (continuous_apply_apply i.succ j.succ).comp continuous_subtype_val
    have hci := (continuous_apply i).comp_continuousOn hc
    have hcj := (continuous_apply j).comp_continuousOn hc
    exact hent.continuousOn.sub (((hsig.comp_continuousOn hci).mul continuousOn_const).mul hcj)
  have hsc : ∀ S : HermR R σ (n + 1),
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :=
    fun S => schur_coe R σ t a S (schurM_mem R σ hinv t a S)
  have hcoe : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    simpa only [hsc] using hM
  have hschur : ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hcoe
  refine ⟨hs0, ha, hc, hschur, ?_⟩

  have hdet : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (continuous_id.matrix_det).comp_continuousOn hcoe
  have hU : IsOpen {y : R ⊗[F] E | IsUnit y} := by
    have : {y : R ⊗[F] E | IsUnit y} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext y; simp [IsUnit]
    rw [this]
    exact hopenU.isOpen_range
  have := hdet.isOpen_inter_preimage hA hU
  exact this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
