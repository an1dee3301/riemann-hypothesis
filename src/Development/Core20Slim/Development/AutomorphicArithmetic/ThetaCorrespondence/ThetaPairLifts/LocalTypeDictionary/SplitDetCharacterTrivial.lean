module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitDetChr
open GlobalTheory.LFun GlobalTheory.Doubling
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.SplitDetChr
theorem GlobalTheory.SplitDetChr.split_det_character_eq_one : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hvT _ _ _ t ht
  obtain ⟨ht1, ht2⟩ := ht
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  haveI : Submodule.IsFullLattice E G.W.L := hTr.geo.hW.lat
  obtain ⟨P0, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame G.W.L v
  have hP := GlobalTheory.AdelicU.Frames.frame_of_rational P0 h1 h2
  set T := Formalism.UG.bc (compFin F E v) t with hTdef
  have hT : ∀ y ∈ latLoc F G.W.L v, T.1 *ᵥ y ∈ latLoc F G.W.L v :=
    GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).1)
  have hT' : ∀ y ∈ latLoc F G.W.L v, (T⁻¹).1 *ᵥ y ∈ latLoc F G.W.L v := by
    rw [hTdef, ← map_inv]
    exact GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).2)
  have hd : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = Matrix.GeneralLinearGroup.det T := by
    refine Units.ext ?_
    show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  have hy := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T hT
  have hy' := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T⁻¹ hT'
  rw [e1]
  show GlobalTheory.Doubling.charAt X.α v _ = 1
  rw [hd]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt X.α v _ hy (by rwa [← map_inv]) (fun w hw => hTr.chars.unrα w ?_)
  show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))
  rw [hw]; exact_mod_cast hvT
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_det_character_trivial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  first | exact @_root_.GlobalTheory.SplitDetChr.split_det_character_eq_one | exact _root_.GlobalTheory.SplitDetChr.split_det_character_eq_one | (intros; apply _root_.GlobalTheory.SplitDetChr.split_det_character_eq_one <;> assumption)
end
