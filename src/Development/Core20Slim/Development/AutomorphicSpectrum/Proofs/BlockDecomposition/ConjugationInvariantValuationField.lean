module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.FieldVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem injective_of_isField {K L : Type} [CommRing K] [Ring L] [Nontrivial L] (hK : IsField K)
    (f : K →+* L) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun y hy => ?_
  by_contra hne
  obtain ⟨z, hz⟩ := hK.mul_inv_cancel hne
  have : f (y * z) = 1 := by rw [hz, map_one]
  rw [map_mul, hy, zero_mul] at this
  exact zero_ne_one this

theorem absBar_finEmb_eq (hK : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  have h1 := minpoly.algHom_eq (finEmb F v τ) (injective_of_isField hK (finEmb F v τ).toRingHom) y
  have h2 := minpoly.algHom_eq (finEmb F v τ') (injective_of_isField hK (finEmb F v τ').toRingHom) y
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  unfold spectralNorm
  rw [h1, h2]

theorem absFin_eq (hK : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absFin F v y = absBar F v (finEmb F v τ y) := by
  refine le_antisymm ((absFin_le_iff F v).2 fun τ' => (absBar_finEmb_eq v hK τ' τ y).le) (le_absFin F v τ y)

theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem exists_valuation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) →
    ∃ W : Valuation (Fv F v ⊗[F] E) ℝ≥0, (∀ a, W a = absFin F v a) ∧ ∀ a, W (sigR (Fv F v) σ a) = W a := by
  intro F E _ _ _ _ _ σ _ v hK
  let τ₀ : E →ₐ[F] FvBar F v := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(valBar F v).comap (finEmb F v τ₀).toRingHom, fun a => ?_, fun a => ?_⟩
  · exact (absFin_eq v hK τ₀ a).symm
  · change absBar F v (finEmb F v τ₀ (sigR (Fv F v) σ a)) = absBar F v (finEmb F v τ₀ a)
    rw [finEmb_sigR]
    exact absBar_finEmb_eq v hK _ _ a

end GlobalTheory.CompanionTheory.KFin.FieldVal

end
