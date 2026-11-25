module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.MonoJac

variable {D : D7}

open GlobalTheory.SeeSaw.SplitLat (colProj colProj_mulVec colMul_rat rat_mulVec_mem_latV mulVec_eq_sum_colMul)

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀)
    (hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L)
    (hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L)
    (h0 : ∀ x ∈ L, d.q0 *ᵥ x ∈ L₀) (hi : ∀ x ∈ L₀, d.i₀ *ᵥ x ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L L₀ v := by
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change GlobalTheory.FinPl.colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change GlobalTheory.FinPl.colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 h0 _ hy
  · rintro ⟨h1, h3, h2⟩
    have hrat : d.e * d.qX + d.i₀ * d.q0 + d.e' * d.qY = 1 := by
      have h : fromRows (fromRows d.qX d.q0) d.qY * fromCols (fromCols d.e d.i₀) d.e' = 1 := by
        rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols,
          GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_i₀,
          GlobalTheory.SeeSaw.SplitLat.qX_e', GlobalTheory.SeeSaw.SplitLat.qY_e,
          GlobalTheory.SeeSaw.SplitLat.qY_i₀, GlobalTheory.SeeSaw.SplitLat.qY_e',
          GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero,
          GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one,
          GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
          fromBlocks_one, fromRows_zero, fromCols_zero, fromBlocks_one]
      rw [← fromCols_mul_fromRows, ← fromCols_mul_fromRows]
      exact (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 h
    have hsum : d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 := by
      have h := congrArg rat hrat
      change (d.e * d.qX + d.i₀ * d.q0 + d.e' * d.qY).map (incA D) = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) at h
      rw [Matrix.map_add _ (map_add (incA D)), Matrix.map_add _ (map_add (incA D)),
        Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_one] at h
      · exact h
      · exact map_zero (incA D)
      · exact map_one (incA D)
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        hsum, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ hi _ h2

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem sumLat_map {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (N : Matrix (Fin n) (Fin n) D.host.E) (w : Fin c → D.host.E) (hM : N * M = 0) (ha : N * a = a * Matrix.diagonal w)
    (hw : ∀ p, w p = 0 ∨ w p = 1) : ∀ x ∈ sumLat M Λ a 𝔟, N *ᵥ x ∈ sumLat M Λ a 𝔟 := by
  rintro _ ⟨y, -, u, hu, rfl⟩
  refine ⟨0, Λ.zero_mem, Matrix.diagonal w *ᵥ u, fun p => ?_, ?_⟩
  · rw [Matrix.mulVec_diagonal]
    rcases hw p with h | h
    · rw [h, zero_mul]; exact (𝔟 p).zero_mem
    · rw [h, one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

theorem sumLat_proj {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (q : Matrix (Fin k) (Fin n) D.host.E) (hM : q * M = 1) (ha : q * a = 0) : ∀ x ∈ sumLat M Λ a 𝔟, q *ᵥ x ∈ Λ := by
  rintro _ ⟨y, hy, u, -, rfl⟩
  rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, Matrix.one_mulVec, Matrix.zero_mulVec,
    add_zero]

theorem mem_sumLat_of {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin k → D.host.E}
    (hy : y ∈ Λ) : M *ᵥ y ∈ sumLat M Λ a 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem colProj_mul {S : HSp D} {ρ m l : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (i : Fin ρ) (N : Matrix (Fin m) (Fin l) D.host.E) : colProj (S := S) q f i * N = colProj (S := S) (q * N) f i := by
  ext k j
  simp only [colProj, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]

theorem colProj_zero {S : HSp D} {ρ m : ℕ} (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    colProj (S := S) (0 : Matrix (Fin ρ) (Fin m) D.host.E) f i = 0 := by
  ext k j
  simp [colProj]

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ}


def cfE' (c : ℕ) (s : Fin ρ → D.host.E) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if q.1 + p.1 + 1 = c then (s p)⁻¹ else 0


end SlopeTestRemainingChoices

open GlobalTheory.SeeSaw.SplitLat (colProj)



end GlobalTheory.AscFin.MonoJac

end
