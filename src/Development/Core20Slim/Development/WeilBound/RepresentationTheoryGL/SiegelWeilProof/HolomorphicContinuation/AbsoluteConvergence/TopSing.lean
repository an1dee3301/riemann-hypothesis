module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G]

def hz (Ht : G → ℝ≥0) (sec : PX m n →ₗ[ℂ] (G → ℂ)) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x

def Top [MeasurableSpace (KR n)] (μ : Measure (KR n)) (ι : GR n →* G) (p q : ℕ) (e : ℤ) (a b : GR n)
    (nb : (Fin n → Fin n → ℝ) → GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (F : G → ℂ) (g : G) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) ∂μ

variable [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_sing [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    (hnb : ∀ x, mR (nb x) = nU (herm x)) (F : G → ℂ) (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hl : ∀ l ∈ Λ, l F = 0) (g : G) : Top μ ι p q e a b nb ψ F g = 0 := by
  unfold Top
  have : ∀ k : KR n, (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) = 0 := fun k =>
    hG.Λsing F hF hinv hl ψ hψ nb hnb g ((k : GR n) * a) b
  simp only [this, mul_zero, integral_zero]

theorem hz_split (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (g : G) :
    ∃ (y : GR n) (K : ℂ) (r : ℝ), 0 < r ∧ ∀ (z : ℂ) (w : GR n), hz Ht sec s₀ z (g * ι w) =
      K * ((r : ℂ) ^ (z - s₀)) * (((hLoc (y * w) : ℝ) : ℂ) ^ (z - s₀) * F0 p q e (y * w)) := by
  obtain ⟨x0, y, S, r, hr, hg, hsp⟩ := hG.split g
  refine ⟨y, S, r, hr, fun z w => ?_⟩
  have h1 := hsp (y * w)
  have e1 : g * ι w = x0 * ι (y * w) := by rw [hg, map_mul, mul_assoc]
  rw [e1]
  simp only [hz]
  rw [h1.1, h1.2 1, hL.vac, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_nonneg _)]
  ring

theorem top_hz [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    {ψ : (Fin n → Fin n → ℝ) → ℂ} {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (z : ℂ) (g : G) : Top μ ι p q e a b nb ψ (hz Ht sec s₀ z) g = cz (z - s₀) * hz Ht sec s₀ z g := by
  obtain ⟨y, K, r, hr, hsp⟩ := hz_split hL hG g
  have e1 : ∀ (k : KR n) x, hz Ht sec s₀ z (g * ι ((k : GR n) * a * nb x * b)) * ψ x =
      (K * (r : ℂ) ^ (z - s₀)) * ((((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := by
    intro k x
    rw [hsp]
    simp only [mul_assoc]
  have e2 : hz Ht sec s₀ z g = K * (r : ℂ) ^ (z - s₀) * (((hLoc y : ℝ) : ℂ) ^ (z - s₀) * F0 p q e y) := by
    have := hsp z 1
    rwa [map_one, mul_one, mul_one] at this
  unfold Top
  simp_rw [e1, MeasureTheory.integral_const_mul]
  have e3 : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ * (K * (r : ℂ) ^ (z - s₀) * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) = (K * (r : ℂ) ^ (z - s₀)) * ((F0 p q e (k : GR n))⁻¹ * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := fun k => by ring
  simp_rw [e3, MeasureTheory.integral_const_mul, hceig, e2]
  ring

end PositivityTheory.Rg.Sw.AbsSt.Vac
