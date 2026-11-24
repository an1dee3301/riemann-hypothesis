module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.ModelPol

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finPr {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem pure_eq {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (finPr φ) := rfl



def pt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain MeasureTheory Filter Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.ThK.ModelPol.pureA_pt {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    _root_.GlobalTheory.WeilM.pureA F f g (_root_.GlobalTheory.ThK.ModelPol.pt x y) = f x * g y := by
  change f (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i))) * g y = f x * g y
  simp only [RingEquiv.apply_symm_apply]



section

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}



end



end GlobalTheory.ThK.ModelPol

end
