module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensorStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInertStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAtStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLagr

theorem exists_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
      ∃ Cy : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) G.W.J) Cy := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw
  have hF := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hT.base v w hvw
  obtain ⟨y, u, hu, hy⟩ := GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert F E σ B hT.base _ _ _ G.W hT.geo.hW hT.geo.even v w hvw hF
  obtain ⟨z, hz⟩ := GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt F E σ B hT.base v w hvw hF u hu
  refine GlobalTheory.T.exists_lagrangian_skewHermitian_completionTensor F E σ hT.base.cm v hF (a + a') G.W.J hT.geo.even hT.geo.hW.skew
    (GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace F E σ B _ _ _ G.W hT.geo.hW) ⟨z * y, ?_⟩
  rw [hy, hz, map_mul]
  ring

end GlobalTheory.InertLagr
