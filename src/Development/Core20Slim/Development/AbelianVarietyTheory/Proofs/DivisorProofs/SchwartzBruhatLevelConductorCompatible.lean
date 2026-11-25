module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.NormedValued

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.PureFix

theorem pureA_fixed : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (m₁ M m₃ : ℕ), 0 < m₁ → 0 < M → 0 < m₃ → (∀ a : κ → AF F, IsMulInt F m₁ a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x) → (∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 → ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1) → (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m₃ : Fv F v)‖) → ψ t = 1) → ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ, ∀ a b : κ → AF F, IsMulInt F (2 * m₁ * M * m₃) a → IsMulInt F (2 * m₁ * M * m₃) b → schr ψ (a, b) (pureA F f g) = pureA F f g := by
  intro F _ _ κ _ ψ g m₁ M m₃ hm₁ hM hm₃ hg hx hψ f a b ha hb
  funext x
  have ha' : IsMulInt F m₁ a := by
    have e : 2 * m₁ * M * m₃ = (2 * M * m₃) * m₁ := by ring
    rw [e] at ha; exact ha.mono
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + a) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i; congr 1; show (x i).1 + (a i).1 = (x i).1; rw [ha.1 i, add_zero]
  have e2 : (fun i => ((x + a) i).2) = (fun i => (x i).2) + fun i => (a i).2 := rfl
  simp only [schr, pureA]
  rw [e1, e2, hg a ha' (fun i => (x i).2)]
  by_cases h0 : g (fun i => (x i).2) = 0
  · simp [h0]
  · have hs : ∀ (c d : κ → AF F), (∀ i, (d i).1 = 0) → (c ⬝ᵥ d).1 = 0 := by
      intro c d hd
      change fstA F (∑ i, c i * d i) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul]; change (c i).1 * (d i).1 = 0; rw [hd i, mul_zero]
    have hnat : ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ), ‖(n : Fv F v)‖ ≤ 1 :=
      fun v n => GlobalTheory.SmoothForms.denom_norm_natCast_le_one v n
    rw [hψ _ ?_ ?_, one_mul]
    · change (x ⬝ᵥ b).1 + (⅟2 : AF F).1 * (a ⬝ᵥ b).1 = 0
      rw [hs x b hb.1, hs a b hb.1, mul_zero, add_zero]
    · intro v
      have hb' : ∀ i, ‖evFin F v (b i)‖ ≤ ‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
        intro i; have := hb.2 v i; push_cast at this; simpa [norm_mul, mul_assoc] using this
      have h2 : ‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖ = 1 := by
        rw [← norm_mul, show (2 : Fv F v) = evFin F v (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul,
          invOf_mul_self, map_one, norm_one]
      have ha2 : ∀ i, ‖evFin F v (⅟2 * a i)‖ ≤ 1 := by
        intro i
        have := ha.2 v i
        push_cast at this
        rw [map_mul, norm_mul]
        calc ‖evFin F v (⅟2 : AF F)‖ * ‖evFin F v (a i)‖
            ≤ ‖evFin F v (⅟2 : AF F)‖ * ‖(2 * m₁ * M * m₃ : Fv F v)‖ := by gcongr
          _ = (‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖) * ‖((m₁ * M * m₃ : ℕ) : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 := by rw [h2, one_mul]; exact hnat v _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), dotProduct, dotProduct, Finset.mul_sum, map_sum, map_sum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [map_mul, norm_mul]
        calc ‖evFin F v (x i)‖ * ‖evFin F v (b i)‖
            ≤ ‖evFin F v (x i)‖ * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr; exact hb' i
          _ = ‖(M : Fv F v) * evFin F v (x i)‖ * ‖((2 * m₁ : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * 1 * ‖(m₃ : Fv F v)‖ := by
              gcongr
              · exact hx x h0 i v
              · exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := by ring
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [← mul_assoc, map_mul, norm_mul]
        calc ‖evFin F v (⅟2 * a i)‖ * ‖evFin F v (b i)‖
            ≤ 1 * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr
              · exact ha2 i
              · exact hb' i
          _ = ‖((2 * m₁ * M : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * ‖(m₃ : Fv F v)‖ := by gcongr; exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := one_mul _

end GlobalTheory.PureFix

end
