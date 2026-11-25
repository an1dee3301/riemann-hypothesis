module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitaryEmbeddingProperties

def ex {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h : Matrix (Fin r) (Fin r) R) : Matrix (Fin n) (Fin n) R :=
  1 + P * (h - 1) * Q

section Gen

variable {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)

theorem ex_mul_P (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * P = P * h := by
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
    add_sub_cancel]

theorem ex_mul_N (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * (1 - P * Q) = 1 - P * Q := by
  have e : Q * (1 - P * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul, sub_self]
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (P * (h - 1)), e, Matrix.mul_zero, add_zero]

theorem ex_mul (hQP : Q * P = 1) (a b : Matrix (Fin r) (Fin r) R) : ex P Q (a * b) = ex P Q a * ex P Q b := by
  have e3 : P * (a - 1) * Q * (P * (b - 1) * Q) = P * ((a - 1) * (b - 1)) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have e4 : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [ex, ex, ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, e3, e4]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

theorem ex_one : ex P Q 1 = 1 := by simp [ex]

theorem ex_map {R' : Type} [CommRing R'] (φ : R →+* R') (h : Matrix (Fin r) (Fin r) R) :
    (ex P Q h).map φ = ex (P.map φ) (Q.map φ) (h.map φ) := by
  simp only [ex, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_one _ (map_zero φ) (map_one φ)]

end Gen

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

def qM (d : HermitianOrthogonalExtensionData A B c ε) : Matrix (Fin A.rank) (Fin B.rank) D.host.E :=
  A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram)

theorem qM_mul (d : HermitianOrthogonalExtensionData A B c ε) : qM d * frameMat B A d.ι = 1 := by
  rw [qM, Matrix.mul_assoc, GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom,
    Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit]

theorem qM_mul_map {R : Type} [CommRing R] (φ : D.host.E →+* R) (d : HermitianOrthogonalExtensionData A B c ε) :
    (qM d).map φ * (frameMat B A d.ι).map φ = 1 := by
  rw [← Matrix.map_mul, qM_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem unitaryEmbedding_matrix_formula (d : HermitianOrthogonalExtensionData A B c ε) (h : GA D A) :
    (matHom B (stabilizerEmbedding d h)).1 = ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (matHom A h).1 := by
  have hr := (embRel_iff d h _).2 rfl
  set P := frameMat B A d.ι
  set C := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * B.gram
  have hG : C * P = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom
  set N : Matrix (Fin B.rank) (Fin B.rank) D.host.E := 1 - P * qM d with hN
  have hC : C * N = 0 := by
    rw [hN, qM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hG,
      Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul, sub_self]
  have h1 : (matHom B (stabilizerEmbedding d h)).1 * N.map (incA D) = N.map (incA D) := by
    ext i j
    exact congr_fun (hr.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hC k) j)) i
  have hNm : N.map (incA D) = (1 : Matrix (Fin B.rank) (Fin B.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) -
      HMul.hMul (P.map (incA D)) ((qM d).map (incA D)) := by
    rw [hN, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.AutFunCounterexample.split_gen (incA D) P (qM d) _ _ ?_ ?_
  · rw [h1, hNm, ex_mul_N _ _ (qM_mul_map _ d)]
  · rw [hr.1, ex_mul_P _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_mul (d : HermitianOrthogonalExtensionData A B c ε) (g h : GA D A) : stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h := by
  apply GlobalTheory.AutFunCounterexample.GA_ext
  rw [map_mul, Units.val_mul, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, map_mul, Units.val_mul,
    ex_mul _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_rational (d : HermitianOrthogonalExtensionData A B c ε) (γ : GA D A) (hγ : γ ∈ GQ A) : stabilizerEmbedding d γ ∈ GQ B := by
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have q2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram = A.gram * qM d := by
    rw [qM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul]
  set P := frameMat B A d.ι
  set Q := qM d
  have q3 : Q * P = 1 := qM_mul d
  have q1 : B.gram * P = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Q * A.gram := by
    have := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) q2
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT,
      GlobalTheory.AutFunCounterexample.gram_herm] at this
  let γ' : GL (Fin B.rank) D.host.E := ⟨ex P Q γE, ex P Q (γE⁻¹ : GL (Fin A.rank) D.host.E),
    by rw [← ex_mul _ _ q3, Units.mul_inv, ex_one], by rw [← ex_mul _ _ q3, Units.inv_mul, ex_one]⟩
  have hu : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram :=
    GlobalTheory.AutFunCounterexample.ext_unitary _ B.gram A.gram P Q q1 q2 q3 _ hγE
  refine Subgroup.mem_subgroupOf.2 ⟨γ', hu, Units.ext ?_⟩
  have hA : (matHom A γ).1 = (γE : Matrix (Fin A.rank) (Fin A.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  show (ex P Q γE).map (incA D) = (matHom B (stabilizerEmbedding d γ)).1
  rw [unitaryEmbedding_matrix_formula, hA, ex_map]


set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) : Continuous (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hf : ∀ {f : GA D A → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)}, Continuous f →
      Continuous fun h => ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (f h) := fun hc =>
    continuous_const.add ((continuous_const.matrix_mul (hc.sub continuous_const)).matrix_mul continuous_const)
  have hv : Continuous fun h : GA D A => (matHom A h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun h : GA D A => (matHom A h⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (unitaryEmbedding_mul d)
  have hc : Continuous fun h => matHom B (stabilizerEmbedding d h) := by
    refine Units.continuous_iff.2 ⟨(hf hv).congr fun h => (unitaryEmbedding_matrix_formula d h).symm, (hf hi).congr fun h => ?_⟩
    have e : (stabilizerEmbedding d h)⁻¹ = stabilizerEmbedding d h⁻¹ := (map_inv φ h).symm
    rw [← map_inv (matHom B), e, unitaryEmbedding_matrix_formula]
  exact Continuous.subtype_mk (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig B.gram) hc fun h => (stabilizerEmbedding d h).2

theorem unitaryEmbedding_continuous_hom_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B :=
  fun d => ⟨continuous_unitaryEmbedding d, unitaryEmbedding_mul d, unitaryEmbedding_rational d⟩

end GlobalTheory.UnitaryEmbeddingProperties
