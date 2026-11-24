module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def iotaW (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.InertLocField.liftT (E := E) v).toAddMonoidHom.comp
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom.toAddMonoidHom

def conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+* w.adicCompletion E :=
  (toCompl (under_eq_of_isInertAt hw)).comp
    ((sigR (Fv F v) σ).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom)

def glueW (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + P.map (iotaW hw)

def InLat {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (u : Fin d → K) : Prop :=
  ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u) i ∈ O

def InLat2 {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (z : Fin d ⊕ Fin d → K) : Prop :=
  InLat O b (z ∘ Sum.inl) ∧ InLat O b (z ∘ Sum.inr)

end GlobalTheory.InertBigCell
