module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocGrpIff
open GlobalTheory.LocGrp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem transfer_back {K : Type} [Field K] {Z : Type} [Fintype Z] [DecidableEq Z] {m : ℕ} {β : Matrix (Fin m) Y K}
    {γ : Matrix Y (Fin m) K} (h : γ * β = 1) {β' : Matrix (Fin m) Z K}
    {γ' : Matrix Z (Fin m) K} (h' : γ' * β' = 1) (τ : Z → Y) (hτ : Function.Surjective τ) (t : Z → K)
    (ht : ∀ r z, β r (τ z) = t z * β' r z) (N : Matrix Y Y K) (z z' : Z) (hN : (γ' * (β * N * γ) * β') z z' = 0) :
    N (τ z) (τ z') = 0 := by
  have e : γ' * (β * N * γ) * β' = γ' * β * N * (γ * β') := by simp only [Matrix.mul_assoc]
  have a0 : ∀ w, (γ' * β) z (τ w) = t w * (1 : Matrix Z Z K) z w := fun w => by
    rw [← h']
    simp only [Matrix.mul_apply, ht, mul_left_comm _ (t w), ← Finset.mul_sum]
  have a1 : ∀ r, r ≠ τ z → (γ' * β) z r = 0 := fun r hr => by
    obtain ⟨w, rfl⟩ := hτ r
    rw [a0, Matrix.one_apply_ne (fun e => hr (by rw [e])), mul_zero]
  have a2 : ∀ w s, t w * (γ * β') s w = (1 : Matrix Y Y K) s (τ w) := fun w s => by
    rw [← h]
    simp only [Matrix.mul_apply, ht, mul_left_comm _ (t w), ← Finset.mul_sum]
  have a3 : t z ≠ 0 := fun e0 => by
    have := a2 z (τ z)
    rw [e0, zero_mul, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have a4 : t z' * (γ' * β * N * (γ * β')) z z' = (γ' * β * N * (1 : Matrix Y Y K)) z (τ z') := by
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [mul_left_comm, a2]
  rw [← e, hN, mul_zero, Matrix.mul_one, Matrix.mul_apply, Finset.sum_eq_single (τ z) (fun r _ hr => by rw [a1 r hr, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), a0, Matrix.one_apply_eq, mul_one] at a4
  exact (mul_eq_zero.1 a4.symm).resolve_left a3

section Witt
variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem flag_cols {g : GA D S} (hg : g ∈ flagN d) : ∃ (T : Mx D ρ ρ) (B : Mx D ρ S₀.rank), GlobalTheory.BesselChar.StrictUp T ∧
    (mt S g - 1) ⬝ d.jX = d.jX ⬝ T ∧ (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B := by
  obtain ⟨⟨T, hT, h1⟩, h2⟩ := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e (GlobalTheory.MixPer.Decomp.linInd d) g).1 hg
  obtain ⟨B, hB⟩ := GlobalTheory.MixPer.Decomp.exists_B d h2
  have h1' : mt S g ⬝ d.jX = d.jX + d.jX ⬝ T := h1
  refine ⟨T, B, hT, ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.one_mul, h1', add_sub_cancel_left]
  · rw [Matrix.sub_mul, Matrix.one_mul, hB, add_sub_cancel_left]

theorem flag_YY {g : GA D S} (hg : g ∈ flagN d) {i j : Fin ρ} (hij : i ≤ j) : (d.pY ⬝ ((mt S g - 1) ⬝ d.jY)) i j = 0 := by
  obtain ⟨T, -, hT, h1, -⟩ := flag_cols d (inv_mem hg)
  have e1 : adj (mt S g⁻¹) ⬝ gA S = gA S ⬝ mt S g := by
    conv_rhs => rw [← inv_inv g, GlobalTheory.MixModel.mt_inv, gA_giA_cancel]
  have e2 : d.pY ⬝ ((mt S g - 1) ⬝ d.jY) = adj ((mt S g⁻¹ - 1) ⬝ d.jX) ⬝ (gA S ⬝ d.jY) := by
    simp only [d.pY_eq, adj_mul, adj_sub, adj_one, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      cancel₂ e1]
  rw [e2, h1, adj_mul, Matrix.mul_assoc, d.gram_XY, Matrix.mul_one]
  change cA D (T j i) = 0
  rw [hT j i hij, RingHom.map_zero]




end Witt


variable {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ}









end GlobalTheory.LocGrpIff


end
