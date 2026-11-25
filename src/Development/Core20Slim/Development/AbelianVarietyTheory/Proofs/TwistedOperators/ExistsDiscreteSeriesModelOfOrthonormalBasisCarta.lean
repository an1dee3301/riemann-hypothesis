module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jm_mul_self {n : ℕ} (e : Fin n → Bool) : Formalism.REAL.Jm e * Formalism.REAL.Jm e = 1 := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem jm_injective {n : ℕ} {e e' : Fin n → Bool} (h : Formalism.REAL.Jm e = Formalism.REAL.Jm e') : e = e' := by
  funext a
  have := congrFun (congrFun h a) a
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at this
  cases he : e a <;> cases he' : e' a <;> simp_all <;> norm_num at this

theorem dsModel_of_onb_cart : ∀ (D : D7), GlobalTheory.Published.DiscreteSeriesUpqExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε) → (∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) → ∃ M : DSModel V S, cart M = C ∧ onb M = O := by
  intro D hDS V S O C h1 h2
  choose lam ε hE hP hG using h1
  choose H i1 i2 σ hσ using fun τ =>
    (GlobalTheory.Published.discreteSeriesExists_iff.1 hDS) V.rank (ε τ) (lam τ) (hP τ)
  have hdet : ∀ τ, IsUnit (O τ).det := fun τ => by
    refine Matrix.isUnit_det_of_left_inverse (B := Formalism.REAL.Jm (ε τ) * ((O τ)ᴴ * gramAt D V τ)) ?_
    rw [Matrix.mul_assoc, hG τ, jm_mul_self]
  have hr : ∀ τ, O τ * (O τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (hdet τ)
  have hl : ∀ τ, (O τ)⁻¹ * O τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
  have hii : ∀ τ, ((O τ)⁻¹)⁻¹ = O τ := fun τ => Matrix.nonsing_inv_nonsing_inv _ (hdet τ)
  let M : DSModel V S :=
    { H := H, nacg := i1, ips := i2, σ := σ, lam := lam, ε := ε, fr := fun τ => (O τ)⁻¹,
      enum := hE, ds := hσ,
      fr_unit := fun τ => (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet τ))
      fr_gram := fun τ => by
        rw [← hG τ]
        calc ((O τ)⁻¹)ᴴ * ((O τ)ᴴ * gramAt D V τ * O τ) * (O τ)⁻¹
            = (O τ * (O τ)⁻¹)ᴴ * gramAt D V τ * (O τ * (O τ)⁻¹) := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = gramAt D V τ := by rw [hr τ]; simp }
  refine ⟨M, ?_, ?_⟩
  · funext τ
    obtain ⟨e', hG', hC⟩ := h2 τ
    have he : e' = ε τ := jm_injective (by rw [← hG', hG τ])
    rw [he] at hC
    show ((O τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (O τ)⁻¹ = C τ
    rw [hii, ← hC, Matrix.mul_assoc, hr, Matrix.mul_one]
  · funext τ
    exact hii τ

end GlobalTheory
