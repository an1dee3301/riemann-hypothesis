module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FstarPer

theorem oh_mul {F : Type} [Field F] [NumberField F] {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) :
    x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

theorem continuous_qf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (h : A F) (B : Matrix ι ι (A F)) : Continuous (qf h B) := by
  unfold qf
  exact continuous_const.mul (continuous_id.dotProduct ((continuous_const (y := B)).matrix_mulVec continuous_id))

theorem fstar_periodic : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  intro F _ _ _ _ lf _ _ ψ hψ ι _ _ M B ρ P _ φ hφ
  have hK : IsCompact (qf (hf F) (Bf B) '' tsupport φ) :=
    IsCompact.image hφ.2 (continuous_qf _ _)
  obtain ⟨N, hN, hNK⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.2.1 _ hK
  have htriv := ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.1
  have key : ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ := by
    intro x hx
    funext u
    by_cases hu : u ∈ tsupport φ
    · have h1 := hNK _ (Set.mem_image_of_mem _ hu)
      have h2 : (N : A F) * x * qf (hf F) (Bf B) u ∈ Oh F := by
        have h3 := oh_mul hx h1
        have h4 : (N : A F) * x * qf (hf F) (Bf B) u = x * ((N : A F) * qf (hf F) (Bf B) u) := by
          ring
        rwa [h4]
      simp [opU, htriv _ h2]
    · have h0 : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [opU, h0]
  refine ⟨N, hN, fun x hx => ⟨key x hx, fun y => ?_⟩⟩
  unfold fstar
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h5 := congrFun (key x hx) u
  simp only [opU] at h5 ⊢
  rw [add_mul, AddChar.map_add_eq_mul, mul_assoc, h5]

end GlobalTheory.CompanionTheory.SW.FstarPer
