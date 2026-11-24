module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
public import Development.Core20Slim.Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
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
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.TypeAtCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_eq_of_congr {n p q : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hs : Formalism.UG.HasSignature G p q) :
    (Finset.univ.filter fun a => ε a = true).card = p ∧ (Finset.univ.filter fun a => ε a = false).card = q := by
  classical
  obtain ⟨hc, Q, hQ⟩ := Formalism.UG.P.sig_data G p q hs
  set p' := (Finset.univ.filter fun a => ε a = true).card with hp'
  set q' := (Finset.univ.filter fun a => ε a = false).card with hq'
  let e1 : Fin p' ≃ {a // ε a = true} := (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])).symm
  let e2 : Fin q' ≃ {a // ¬ ε a = true} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simp [hq'])).symm
  let e : Fin p' ⊕ Fin q' ≃ Fin n := (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl _)
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hJ : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    rw [← h]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hQ' : (P⁻¹.submatrix id e)ᴴ * G * P⁻¹.submatrix id e = Formalism.UG.Jpq p' q' := by
    have : (P⁻¹.submatrix id e)ᴴ * G * P⁻¹.submatrix id e = ((P⁻¹)ᴴ * G * P⁻¹).submatrix e e := by
      ext i j; simp [Matrix.mul_apply]
    rw [this, hJ]
    have h1 : ∀ a, ε (e (Sum.inl a)) = true := fun a => (e1 a).2
    have h2 : ∀ a, ¬ ε (e (Sum.inr a)) = true := fun a => (e2 a).2
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2]
    split_ifs <;> simp
  have hn : n = p' + q' := by
    have := Fintype.card_congr e
    simpa using this.symm
  have h1 := Formalism.UG.P.sig_dim G Q hQ _ hQ'
  have h2 := Formalism.UG.P.sig_dim G _ hQ' Q hQ
  simp only [Fintype.card_fin] at h1 h2 hc
  omega

theorem conj_mem {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

section Pred

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {S : SPar}
  {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)} {lam : Fin V.rank → ℝ} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

end Pred

variable {D : D7} {X : ThetaX D}


end GlobalTheory.TypeAtCompare

end
