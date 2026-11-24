module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem linearIndependent_gact {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent E (gact σ g X) := by
  have hker : LinearMap.ker
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y h => ?_
    have h1 : gact σ g (fun _ : Fin 1 => x) = gact σ g (fun _ : Fin 1 => y) :=
      funext fun _ => h
    have h2 := congrArg (gact σ g⁻¹) h1
    rw [gact_inv_gact, gact_inv_gact] at h2
    exact congrFun h2 0
  have h3 : gact σ g X =
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) ∘ X := by
    funext a
    rfl
  rw [h3]
  exact hX.map' (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) hker

theorem gact_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J)
    {T : Matrix (Fin n) (Fin n) E} {X : Fin n → Fin M → E} (hX : X ∈ framesE σ J T) :
    gact σ g X ∈ framesE σ J T :=
  ⟨linearIndependent_gact σ g hX.1, (gramE_gact σ g X).trans hX.2⟩

theorem tsum_framesOne : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (rr : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → UJ (σ : E →+* E) (hypOne J)), (∀ q, gact σ (rr q) q.1 = e0 E M) → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), f X.1 = ∑' q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∑' X : framesOne σ J n, f (gact σ (rr q)⁻¹ X.1) := by
  intro F E _ _ _ σ M J n rr hrr f
  have hrow : ∀ (q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))
      (X : framesOne σ J n), gact σ (rr q)⁻¹ X.1 0 = q.1 0 := by
    intro q X
    have h := congrArg (gact σ (rr q)⁻¹) (hrr q)
    rw [gact_inv_gact] at h
    have h0 := congrFun h 0
    have hX : X.1 0 = e0 E M 0 := X.2.2
    change ((((rr q)⁻¹ : UJ (σ : E →+* E) (hypOne J)) : GL (Fin (M + 2)) E) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X.1 0 = q.1 0
    rw [hX, h0]
    rfl
  let m : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) × framesOne σ J n →
      framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :=
    fun p => ⟨gact σ (rr p.1)⁻¹ p.2.1, gact_mem_framesE σ _ p.2.2.1⟩
  have hinj : Function.Injective m := by
    rintro ⟨q, X⟩ ⟨q', X'⟩ h
    have h1 : gact σ (rr q)⁻¹ X.1 = gact σ (rr q')⁻¹ X'.1 := congrArg Subtype.val h
    have hq : q = q' := by
      apply Subtype.ext
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      rw [← hrow q X, ← hrow q' X', h1]
    subst hq
    have h2 := congrArg (gact σ (rr q)) h1
    rw [gact_gact_inv, gact_gact_inv] at h2
    exact Prod.ext rfl (Subtype.ext h2)
  have hsurj : Function.Surjective m := by
    rintro ⟨Y, hY⟩
    have hq : (fun _ : Fin 1 => Y 0) ∈
        framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
      refine ⟨hY.1.comp (fun _ : Fin 1 => (0 : Fin (n + 1)))
        (Function.injective_of_subsingleton _), ?_⟩
      funext a b
      exact congrFun (congrFun hY.2 0) 0
    let q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := ⟨_, hq⟩
    have hX : gact σ (rr q) Y ∈ framesOne σ J n :=
      ⟨gact_mem_framesE σ _ hY, congrFun (hrr q) 0⟩
    exact ⟨(q, ⟨_, hX⟩), Subtype.ext (gact_inv_gact σ (rr q) Y)⟩
  let e := Equiv.ofBijective m ⟨hinj, hsurj⟩
  rw [← e.tsum_eq (fun Y => f Y.1), ENNReal.tsum_prod']
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
