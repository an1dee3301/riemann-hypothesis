module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaustStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaCountCompactFiniteStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxLatticeCountRatioStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Order.Real

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CntLarge

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def orbitHom (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) :
    (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun X := actW (AF F) σ J h (ratTup (AF F) X)
  map_zero' := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct]
  map_add' X Y := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
      TensorProduct.tmul_add]

theorem count_le (hpack : ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (Λ : Type) [AddCommGroup Λ]
      (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤
        ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) *
          ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l))
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r₀ r : ℝ} (h0 : 0 < r₀) (hr : r₀ ≤ r) :
    ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
          (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E))) ≤
      ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M)) *
        (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
          (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
            (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E)))) := by
  classical
  set e := orbitHom σ J h with he
  have key := hpack d b M (Fin 1 → Fin M → E) e N r₀ r h0 hr
  have hsplit : ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin 1 → Fin M → E)]
    refine add_le_add (by rw [Set.indicator_apply]; split_ifs <;> simp) ?_
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X))]
    refine le_of_eq (tsum_congr fun X => ?_)
    by_cases hX : X = 0 <;> simp [hX]
  have hle : ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X))]
    exact ENNReal.tsum_le_tsum fun X => Set.indicator_le_self _ _ _
  exact hle.trans (key.trans (mul_le_mul_right hsplit _))

theorem cnt_large : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ) (r₀ : ℝ), 0 < N → 0 < r₀ → ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * M)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM μ 𝓕 hμ h𝓕 d b N r₀ hN h0
  have hvol : μ 𝓕 < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  have hcomp : IsCompact (box b N r₀ : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    (GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hσ d b 1 M).1 N r₀ hN
  have hcnt := GlobalTheory.T.theta_count_compact_finite F E σ hσ M J hJ hM μ 𝓕 hμ h𝓕 _ hcomp
  set B : ℝ≥0∞ := μ 𝓕 + cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
    (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) with hB
  have hBtop : B ≠ ⊤ := (ENNReal.add_lt_top.2 ⟨hvol, hcnt⟩).ne
  set k := 2 * Module.finrank ℚ F * M with hk
  refine ⟨(5 / r₀) ^ k * B.toReal, fun r hr => ?_⟩
  have hpt : ∀ h : HA (AF F) σ J, _ := fun h => count_le (fun d b M Λ _ e N r R => GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hσ d b M Λ e N r R)
    σ J h⁻¹ b N h0 hr
  have hr0 : 0 ≤ r := h0.le.trans hr
  calc cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
      ≤ ∫⁻ h in 𝓕, ENNReal.ofReal ((5 * r / r₀) ^ k) *
          (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
            (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))) ∂μ :=
        lintegral_mono fun h => hpt h
    _ = ENNReal.ofReal ((5 * r / r₀) ^ k) * B := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const]
        simp [hB, cntI]
    _ = ENNReal.ofReal ((5 / r₀) ^ k * B.toReal * r ^ k) := by
        have : (5 / r₀) ^ k * B.toReal * r ^ k = (5 * r / r₀) ^ k * B.toReal := by
          rw [show 5 * r / r₀ = 5 / r₀ * r by ring, mul_pow]; ring
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hBtop]

end GlobalTheory.CompanionTheory.SW.CntLarge
