module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def ptAt (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) : w.adicCompletion E →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.AdelicU.Supp.singleTens E v).comp (InertChart.complEquiv hw h).symm.toRingHom.toNonUnitalRingHom

def locW (h : w.under (𝓞 F) = v) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

def kap (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    Matrix (Fin n) (Fin m) (w.adicCompletion E) →+ Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom).comp
    { toFun := fun x => A * xᵀ * Bᵀ
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul] }

variable (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem kap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x : Matrix (Fin n) (Fin m) (w.adicCompletion E)) : kap hw h A B x = (A * xᵀ * Bᵀ).map (ptAt hw h) := rfl

theorem ptAt_apply (z : w.adicCompletion E) :
    ptAt hw h z = GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z) := rfl

theorem locW_ptAt (z : w.adicCompletion E) : locW h (ptAt hw h z) = z := by
  change toCompl h (compFin F E v (GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
  exact (InertChart.complEquiv hw h).apply_symm_apply z

theorem at_ptAt (z : w.adicCompletion E) : At (evFin F v) (ptAt hw h z) :=
  GlobalTheory.ThK.at_evFin_iff.2 ⟨fun u => GlobalTheory.AdelicU.Supp.compInf_singleTens u v _,
    fun u hu => GlobalTheory.AdelicU.Supp.compFin_singleTens_ne hu _⟩

theorem ptAt_locW {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : ptAt hw h (locW h z) = z := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ThK.at_evFin_iff.1 hz
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun u => ?_) fun u => ?_
  · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compInf_singleTens, h1 u]
  · by_cases e : u = v
    · subst e
      rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
      exact (InertChart.complEquiv hw h).symm_apply_apply _
    · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_ne e, h2 u e]

end GlobalTheory.InertCoord

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem cA_ptAt (σ : E →ₐ[F] E) {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (z : w.adicCompletion E) :
    cA σ (ptAt hw h z) = ptAt hw h (c z) := by
  have e1 : ∀ y : AE F E, cA σ y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e1, ptAt_apply, GlobalTheory.AdelicU.Supp.sigR_singleTens, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((InertChart.complEquiv hw h).symm z)
  change c (InertChart.complEquiv hw h ((InertChart.complEquiv hw h).symm z)) = _ at this
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

theorem inclR_mul_ptAt (x : E) (z : w.adicCompletion E) :
    inclR (F := F) (AF F) x * ptAt hw h z = ptAt hw h (algebraMap E (w.adicCompletion E) x * z) := by
  rw [mul_comm, ptAt_apply, GlobalTheory.AdelicU.Supp.singleTens_mul, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, mul_comm]
  congr 1
  change toCompl h (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [GlobalTheory.AdelicU.Supp.compFin_one_tmul, toCompl_tmul, map_one, one_mul]

end GlobalTheory.InertCoord

end
