module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.UnipCocompact

open GlobalTheory.UnipFlagCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem unipMin_eq_radSet (X : Matrix (Fin n) (Fin r) E) :
    unipMin σ J X = radSet σ J X Fin.val := by
  ext u
  constructor
  · rintro ⟨B, hB, hd, hX, hz⟩
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * (B - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      exact congrArg (· - adMat F X) hX
    refine ⟨fun i => ⟨fun j => (B - 1) j i, fun j hij => ?_, ?_⟩, hz⟩
    · rcases (Fin.le_def.2 hij).eq_or_lt with e | e
      · subst e; simp [hd]
      · simp [hB e, e.ne']
    · funext k
      exact congrFun (congrFun e k) i
  · rintro ⟨h1, h2⟩
    choose a ha ha' using h1
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * Matrix.of (fun j i => a i j) := by
      ext k i
      exact congrFun (ha' i) k
    refine ⟨1 + Matrix.of (fun j i => a i j), fun i j hij => ?_, fun i => ?_, ?_, h2⟩
    · have hij' : j < i := hij
      simp [ha j i hij'.le, hij'.ne']
    · simp [ha i i le_rfl]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul]
      exact (add_sub_cancel _ _).symm

theorem closure_radSet_subset (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {X : Matrix (Fin n) (Fin r) E}
    (hC : LinearIndependent E Xᵀ) (h0 : cT (σ : E →+* E) X * J * X = 0) {g : HA (AF F) σ J}
    (hg : g ∈ Subgroup.closure (radSet σ J X Fin.val)) : g ∈ radSet σ J X Fin.val := by
  obtain ⟨L, hL, hLL⟩ := exists_dual hσ hJ X hC h0
  have hd : ∀ j : Fin r, (j : ℕ) < r := fun j => j.2
  have he := idem_complete hσ hJ X L hL h0 hLL
  have hs := fam_st (adj_mul hσ hJ) (adj_adj hσ hJ) (idem (F := F) X L) (Fin.val : Fin r → ℕ) r
  have h1 := GlobalTheory.TwoStepUnipotent.st_one (adj_mul hσ hJ) (adj_adj hσ hJ)
  rw [mem_radSet_iff hσ hJ X L hL h0 hLL hd]
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (mem_radSet_iff hσ hJ X L hL h0 hLL hd x).1 hx
  | one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _
  | mul x y _ _ hx hy =>
    have e : (HA.mat _ σ J (x * y)).1 = (HA.mat _ σ J x).1 * (HA.mat _ σ J y).1 := rfl
    rw [e]
    generalize (HA.mat _ σ J x).1 = a at hx ⊢
    generalize (HA.mat _ σ J y).1 = b at hy ⊢
    have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
  | inv x _ hx =>
    have := raise_st (adj_mul hσ hJ) (adj_adj hσ hJ) hs 0 hx
    rwa [map_sub, adj_mat hσ hJ, h1] at this

theorem linearIndependent_of_isWittFrame (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) : LinearIndependent E Xᵀ := by
  have e : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' hσ hJ, cT_gram hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  refine Matrix.mulVec_injective_iff.1 fun v w h => ?_
  have := congrArg ((cT (σ : E →+* E) Y * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] using this

theorem unipMin_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ u ∈ unipMin σ J X, ∃ δ ∈ ratPts σ J, δ ∈ unipMin σ J X ∧ ∃ c ∈ C, c ∈ unipMin σ J X ∧ u = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  have hσ := sigma_sigma h
  have hC := linearIndependent_of_isWittFrame hσ hJ hW
  obtain ⟨K, hK, hcov⟩ := closure_radSet_cocompact hσ hJ X hC hW.xx Fin.val
  have hsub : ∀ g : Subgroup.closure (radSet σ J X Fin.val), g.1 ∈ unipMin σ J X := fun g => by
    rw [unipMin_eq_radSet]
    exact closure_radSet_subset hσ hJ hC hW.xx g.2
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun u hu => ?_⟩
  rw [unipMin_eq_radSet] at hu
  obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨u, Subgroup.subset_closure hu⟩
  exact ⟨γ.1, hγ, hsub γ, k.1, ⟨k, hk, rfl⟩, hsub k, congrArg Subtype.val e⟩

end GlobalTheory.CompanionTheory.UnipCocompact
