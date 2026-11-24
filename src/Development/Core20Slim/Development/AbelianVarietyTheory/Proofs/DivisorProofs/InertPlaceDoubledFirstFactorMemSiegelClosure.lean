module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecompositionStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDblGen

theorem inlD_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv k hk
  obtain ⟨k₁, hk₁, k₂, hk₂, h₁, h₂, rfl⟩ := GlobalTheory.T.inertPlace_stabilizer_two_factor_decomposition F E σ B a a' G X om om' hT v w hv k hk
  rw [map_mul]
  obtain ⟨n₁, hn₁, p₁, hp₁, e₁⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₁ hk₁ h₁
  obtain ⟨n₂, hn₂, p₂, hp₂, e₂⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₂ hk₂ h₂
  rw [e₁, e₂]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (s _ (Or.inr hn₁)) (s _ (Or.inl hp₁)))
    (Subgroup.mul_mem _ (s _ (Or.inr hn₂)) (s _ (Or.inl hp₂)))

end GlobalTheory.InertDblGen
