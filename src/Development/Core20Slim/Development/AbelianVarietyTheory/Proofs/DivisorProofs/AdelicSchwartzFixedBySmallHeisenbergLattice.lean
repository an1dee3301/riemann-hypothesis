module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.FinSuppHeis

theorem norm_le_of_finDiv {F : Type} [Field F] [NumberField F] {N : ℕ} {a : AF F} (h : GlobalTheory.FinSupp.FinDiv F N a)
    (v : HeightOneSpectrum (𝓞 F)) : ‖evFin F v a‖ ≤ ‖(N : Fv F v)‖ := by
  obtain ⟨b, hb, e⟩ := h v
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((GlobalTheory.SuppDen.norm_le_one_iff_mem v b).mpr hb)

theorem heis_fix_finDiv : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨m₀, hm₀, h⟩ := GlobalTheory.ThetaLevel.heis_fix (F := F) (κ := κ) ψ hψ Φ hΦ
  refine ⟨m₀, hm₀, fun w hw => ?_⟩
  exact h w.1 w.2 ⟨fun i => (hw i).1, fun v i => norm_le_of_finDiv (hw i).2.1 v⟩
    ⟨fun i => (hw i).2.2.1, fun v i => norm_le_of_finDiv (hw i).2.2.2 v⟩

end GlobalTheory.FinSuppHeis
