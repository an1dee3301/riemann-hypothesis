module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSoluti
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl (F := F)) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (P Q : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.TransportBack.transport_back | exact GlobalTheory.TransportBack.transport_back | (intros; apply GlobalTheory.TransportBack.transport_back <;> assumption)
