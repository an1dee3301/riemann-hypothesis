module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormDiagonalizesOverField
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLawsStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionDiagonalGramTuplesStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransUC

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext a b
  simp [cT, sigR_inclR]

theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, hR, hform, gramE, hE, ratTup, JR, map_sum, map_mul, sigR_inclR]

theorem gramE_herm (σ : E →ₐ[F] E) (hσ : ∀ x : E, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → E) (a b : Fin n) :
    σ (gramE σ J X b a) = gramE σ J X a b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramE, hE, hform, map_sum, map_mul, RingHom.coe_coe, AlgHom.commutes]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hσ, hJ]
  ring

theorem inclR_algebraMap (d : F) :
    inclR (E := E) R (algebraMap F E d) = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  change (1 : R) ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d) ⊗ₜ[F] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

end SlopeTestRemainingChoices

theorem trans_uc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR R σ J Y = (gramE σ J X).map (inclR R) →
    ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  intro F E _ _ _ _ _ σ hCM R _ _ uc n M J hJ X Y hdet hY
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  have hT : IsHermND σ (gramE σ J X) := ⟨gramE_herm σ hσ J hJ.1 X, hdet⟩
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian F E σ hCM n _ hT
  set G : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g : Matrix (Fin n) (Fin n) E).map (inclR R) with hG
  set G' : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (inclR R) with hG'
  have hGG' : G * G' = 1 := by
    have h1 : (g : Matrix (Fin n) (Fin n) E) * ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 :=
      Units.mul_inv g
    have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map (inclR (F := F) R)) h1
    simp only [Matrix.map_mul] at h2
    rw [hG, hG', h2, Matrix.map_one _ (map_zero _) (map_one _)]
  let D' : Fin n → Rˣ := fun i => Units.map (algebraMap F R).toMonoidHom (D i)
  have hdiag : cT (sigR R σ) G * (gramE σ J X).map (inclR R) * G =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [hG, cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hg]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [D', inclR_algebraMap]
    · simp [Matrix.diagonal_apply_ne _ hab, hab]
  have P := fun (Z : Fin n → Fin M → R ⊗[F] E) (H H' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =>
    GlobalTheory.T.gram_right_mul_action_laws F E σ hCM R M n J Z H H'
  have hX1 : gramR R σ J (rmul R (ratTup R X) G) =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [(P _ G G).1, gramR_ratTup, hdiag]
  have hY1 : gramR R σ J (rmul R Y G) = gramR R σ J (rmul R (ratTup R X) G) := by
    rw [hX1, (P _ G G).1, hY, hdiag]
  obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_diagonal_gram_tuples F E σ hCM R uc M J hJ n D' _ _ hX1 hY1
  refine ⟨h, ?_⟩
  have undo : ∀ Z : Fin n → Fin M → R ⊗[F] E, rmul R (rmul R Z G) G' = Z := by
    intro Z
    rw [(P Z G G').2.1, hGG', (P Z G G').2.2.1]
  calc actW R σ J h (ratTup R X)
      = actTup R (HA.mat R σ J h) (rmul R (rmul R (ratTup R X) G) G') := by
        rw [undo]; rfl
    _ = rmul R (actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G)) G' :=
        (P _ G' G').2.2.2 _
    _ = rmul R (rmul R Y G) G' := by
        rw [show actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G) = rmul R Y G from hh]
    _ = Y := undo Y

end GlobalTheory.CompanionTheory.SW.TransUC
