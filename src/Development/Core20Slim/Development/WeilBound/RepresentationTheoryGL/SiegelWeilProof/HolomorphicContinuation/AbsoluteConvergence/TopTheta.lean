module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamCont
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopSing
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_theta [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    (hnbc : Continuous nb) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (I1 : G → ℂ) (hIc : Continuous I1)
    (hTS : ∀ (g : G) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I1 (g * ι ((k : GR n) * y)) ∂μ =
      I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * y) ∂μ) (g : G) :
    Top μ ι p q e a b nb ψ I1 g = cz 0 * I1 g := by
  have hswap : ∀ Φ : GR n → ℂ, Continuous Φ →
      ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ =
      ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * Φ ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    intro Φ hΦ
    have hcont : Continuous (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine Continuous.mul ?_ (Continuous.mul ?_ (hψc.comp continuous_snd))
      · exact ((continuous_weight_factor hD p q e).comp (continuous_subtype_val.comp continuous_fst)).inv₀
          (fun z => spherical_section_ne_zero hD p q e _)
      · exact hΦ.comp ((((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
          (hnbc.comp continuous_snd)).mul continuous_const)
    have hsupp : HasCompactSupport (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine HasCompactSupport.intro' (K := univ ×ˢ tsupport ψ) (isCompact_univ.prod hψs)
        (isClosed_univ.prod (isClosed_tsupport ψ)) ?_
      intro z hz
      have hz2 : z.2 ∉ tsupport ψ := fun h => hz ⟨mem_univ _, h⟩
      simp [image_eq_zero_of_notMem_tsupport hz2]
    have hint := hcont.integrable_of_hasCompactSupport (μ := μ.prod volume) hsupp
    calc _ = ∫ k : KR n, (∫ x, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) ∂μ := by
          congr 1
          funext k
          exact (integral_const_mul _ _).symm
      _ = ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ) :=
          integral_integral_swap
            (f := fun (k : KR n) (x : Fin n → Fin n → ℝ) =>
              (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) hint
      _ = _ := by
          congr 1
          funext x
          rw [← integral_mul_const]
          congr 1
          funext k
          simp only [mul_assoc]
  have h1 := hswap (fun y => I1 (g * ι y)) (hIc.comp (continuous_const.mul hιc))
  have h2 := hswap (F0 p q e) (continuous_weight_factor hD p q e)
  have hc := hceig 0 1
  simp only [Complex.cpow_zero, one_mul, mul_one, weight_factor_one] at hc
  unfold Top
  rw [h1]
  simp_rw [hTS g]
  have hpull : ∫ x, (I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x =
      I1 g * ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hpull, ← h2, hc, mul_comm]

end PositivityTheory.Rg.Sw.AbsSt.Vac
