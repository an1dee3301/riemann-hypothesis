module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem coefBound_two :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ a c : H, Sm ε σ a → a ≠ 0 → Sm ε σ c → c ≠ 0 → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ γ : H → H → ℂ, (∀ b, Sm ε σ b → SobFun ε σ (γ b)) → (∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w))) → ∀ M : ℝ, 0 ≤ M → (∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ‖γ (σ g' c) (σ g a)‖ ≤ M * (1 + hs g) ^ N * (1 + hs g') ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖γ b w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ hS hB a c ha ha0 hc hc0 N
  obtain ⟨Sa, Ca, hSa, hCa, ba⟩ := hB a ha ha0 N
  obtain ⟨Sc, Cc, hSc, hCc, bc⟩ := hB c hc hc0 N
  refine ⟨Sa ++ Sc, Ca * Cc, words_append hSa hSc, mul_nonneg hCa hCc, ?_⟩
  intro γ h1 h2 M hM hγ b w hb hw
  have step : ∀ g' ∈ UJset ε, ‖γ (σ g' c) w‖ ≤ (Ca * M * sobNorm σ Sa w) * (1 + hs g') ^ N := by
    intro g' hg'
    obtain ⟨ℓ, hℓ, e⟩ := (h1 _ (hc.translate hS.1 hg')).exists_ext
    have hp : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have := ba ℓ hℓ (M * (1 + hs g') ^ N) (mul_nonneg hM hp) (fun g hg => by
      rw [e _ (ha.translate hS.1 hg)]
      exact (hγ g hg g' hg').trans (le_of_eq (by ring))) w hw
    rw [e _ hw] at this
    exact this.trans (le_of_eq (by ring))
  obtain ⟨ℓ, hℓ, e⟩ := (h2 w hw).exists_ext
  have n1 := sobNorm_nonneg σ Sa w
  have n2 := sobNorm_nonneg σ Sc w
  have n3 := sobNorm_nonneg σ Sa b
  have n4 := sobNorm_nonneg σ Sc b
  have key := bc ℓ hℓ (Ca * M * sobNorm σ Sa w) (by positivity) (fun g hg => by
    rw [e _ (hc.translate hS.1 hg), norm_star]
    exact step g hg) b hb
  rw [e _ hb, norm_star] at key
  rw [sobNorm_append, sobNorm_append]
  refine key.trans ?_
  calc Cc * (Ca * M * sobNorm σ Sa w) * sobNorm σ Sc b
      = Ca * Cc * M * sobNorm σ Sc b * sobNorm σ Sa w := by ring
    _ ≤ _ := by gcongr <;> linarith

end GlobalTheory.TypeSum
