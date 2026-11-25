module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.StatementA
public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.RealPlaceAnalysis.StatementU
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

theorem vminus_coef : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  intro V _ _ n ε E Λ u hg hu hΛ F hF a b hab
  have hkr : KRel ε (arrE E 1) := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  have hku : KUnit ε E := isUnitary_kUnit ε E hu

  let φ : Arr V n 1 →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ u).comp ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V)
      (fun _ => (a, b))).comp (arrOf V n 1))
  suffices hle : Vminus ε E Λ u ≤ LinearMap.ker φ by
    have h0 : φ F = 0 := hle hF
    simpa [φ] using h0

  refine iSup₂_le fun y hy => ?_
  obtain ⟨-, μ, ⟨c, d, hdc, -, rfl⟩, hyh⟩ := hy
  rw [(kLow _ n ε (arrE E 1) _ y hkr hyh).1]
  refine Submodule.span_le.2 ?_
  rintro z ⟨w, hw, rfl⟩

  obtain ⟨ν, hht, hν⟩ := GlobalTheory.Jet.VminusComp.word_weight hkr hyh.1 w hw
  have hcw := GlobalTheory.Jet.VminusComp.comp_weight hν a b
  have hne : Λ ≠ ν - root a b := by
    intro h
    have h1 := congrArg GlobalTheory.Jet.VminusComp.ht h
    rw [GlobalTheory.Jet.VminusComp.ht_sub, GlobalTheory.Jet.VminusComp.ht_root] at h1
    rw [GlobalTheory.Jet.VminusComp.ht_add, GlobalTheory.Jet.VminusComp.ht_root] at hht
    have h2 : ((d : ℕ) : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast hdc
    have h3 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

  have h0 := kWtOrth V n ε E Λ (ν - root a b) u _ hku hΛ.1 hcw hne
  simpa [φ, arrOf] using h0

end GlobalTheory.SphJet
