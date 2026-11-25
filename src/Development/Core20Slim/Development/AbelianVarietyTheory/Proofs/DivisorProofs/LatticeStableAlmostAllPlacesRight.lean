module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open Matrix
namespace GlobalTheory.AdelMatLatRight


open NumberField IsDedekindDomain in
open Matrix in
theorem _root_.GlobalTheory.AdelMatLatRight.transpose_mem_latAtV {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (w : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y w, γᵀ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y X w := by
  intro γ hγ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV at hγ ⊢
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    rw [transpose_smul]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, vecMulVec_apply, mul_comm]
  | zero => simpa using zero_mem _
  | add u v _ _ hu hv => simpa [transpose_add] using add_mem hu hv
  | neg u _ hu => simpa [transpose_neg] using neg_mem hu


end GlobalTheory.AdelMatLatRight

end
