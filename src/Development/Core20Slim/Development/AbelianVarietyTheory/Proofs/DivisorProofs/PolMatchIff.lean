module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.PolynomialMatching

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolMatchOn (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem polMatch_iff (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) :
    PolMatch B G X R Rf Φ Φ' ↔ ∃ T : Finset (Pl F), X.T ⊆ T ∧ PolMatchOn B G X R Rf T Φ Φ' := Iff.rfl

end GlobalTheory.ThK.PolynomialMatching
