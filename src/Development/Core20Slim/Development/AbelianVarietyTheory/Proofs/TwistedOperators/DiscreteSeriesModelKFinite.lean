module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.KFinStruct

section Model

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.KFinVec

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kFin_eq : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ = kFinSub ε σ :=
  le_antisymm (sSup_le fun W hW _ hw => ⟨W, hW.1, hw, hW.2⟩)
    fun _ ⟨W, h1, h2, h3⟩ => (le_sSup (a := W) ⟨h1, h3⟩ : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) h2

theorem conj_lie' {A B G G' Y : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (hG : Aᴴ * G * A = G')
    (hY : Yᴴ * G + G * Y = 0) : (B * Y * A)ᴴ * G' + G' * (B * Y * A) = 0 := by
  rw [← hG]
  calc (B * Y * A)ᴴ * (Aᴴ * G * A) + Aᴴ * G * A * (B * Y * A)
      = Aᴴ * Yᴴ * (A * B)ᴴ * G * A + Aᴴ * G * (A * B) * Y * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * (Yᴴ * G + G * Y) * A := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY]; simp

theorem exp_smul_conj' {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Q * NormedSpace.exp (t • X) * Q⁻¹ = NormedSpace.exp (t • (Q * X * Q⁻¹)) := by
  rw [← Matrix.exp_conj Q _ hQ, Matrix.mul_smul, Matrix.smul_mul]

theorem model (h : GlobalTheory.Published.KFiniteVectorsUnitary) {lam : Fin n → ℝ} (hσ : IsDS ε lam σ)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = G) :
    (∃ p : kFinSub ε σ, p ≠ 0) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ v : kFinSub ε σ, ∃ w : kFinSub ε σ,
      HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0) ∧
    ∀ B : Submodule ℂ (kFinSub ε σ), B ≠ ⊥ →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ v w : kFinSub ε σ, v ∈ B →
        HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0 → w ∈ B) → B = ⊤ := by
  haveI := hσ.1
  haveI := hσ.2.1
  obtain ⟨-, -, hd, hst, hirr⟩ := h.of_isDS hσ
  have hdet := (isUnit_iff_isUnit_det _).1 hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hG' : (P⁻¹)ᴴ * G * P⁻¹ = Jm ε := by
    rw [← hJ]
    calc _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp
  refine ⟨?_, fun X hX v => ?_, fun B hB hS => ?_⟩
  · by_contra hne
    push_neg at hne
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    obtain ⟨y, hy, hy'⟩ := hd.exists_mem_open isOpen_compl_singleton ⟨x, hx⟩
    exact hy' (congrArg Subtype.val (hne ⟨y, hy⟩))
  · have hY : inG ε (P * X * P⁻¹) := conj_lie' h1 hG' hX
    refine ⟨⟨dRep σ (P * X * P⁻¹) v, hst _ hY _ v.2⟩, ?_⟩
    simp only [exp_smul_conj' hP]
    exact h.hasDerivAt hσ.2.2.1 hσ.2.2.2.1 v.2 hY
  · have hle : B.map (kFinSub ε σ).subtype ≤ kFinSub ε σ := Submodule.map_subtype_le _ _
    have hs : IsLieStable ε σ (B.map (kFinSub ε σ).subtype) := by
      rintro Y hY _ ⟨v, hv, rfl⟩
      refine ⟨⟨dRep σ Y v, hst _ hY _ v.2⟩, hS (P⁻¹ * Y * P) (conj_lie' h2 hJ hY) v _ hv ?_, rfl⟩
      have e : P * (P⁻¹ * Y * P) * P⁻¹ = Y := by
        calc _ = (P * P⁻¹) * Y * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [h2]; simp
      simp only [exp_smul_conj' hP, e]
      exact h.hasDerivAt hσ.2.2.1 hσ.2.2.2.1 v.2 hY
    rcases hirr _ hle hs with e | e
    · exact absurd ((Submodule.map_injective_of_injective (kFinSub ε σ).injective_subtype)
        (e.trans (Submodule.map_bot _).symm)) hB
    · exact (Submodule.map_injective_of_injective (kFinSub ε σ).injective_subtype)
        (e.trans (Submodule.map_subtype_top _).symm)

end Model

end GlobalTheory.KFinStruct
