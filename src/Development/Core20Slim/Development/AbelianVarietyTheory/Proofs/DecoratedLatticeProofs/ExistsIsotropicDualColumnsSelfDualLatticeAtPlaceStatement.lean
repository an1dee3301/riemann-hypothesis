module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
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
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX * b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' * (gA S * c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  let c : Mx D S.rank ρ := d.jX * b
  change adj c' * (gA S * c) = ε • (1 : Mx D ρ ρ) at hcc
  have hcc0 : adj c * (gA S * c) = 0 := by
    dsimp only [c]
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b,
      ← Matrix.mul_assoc (adj d.jX), d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  have hcc' : adj c * (gA S * c') = ε • (1 : Mx D ρ ρ) := by
    have h := congrArg adj hcc
    rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at h
  let H : Mx D ρ ρ := adj c' * (gA S * c')
  have hHint (i j : Fin ρ) : H i j ∈ intAt D (· = v) := by
    have hgram : H i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
      simp only [H, hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Finset.mul_sum, mul_assoc]
    rw [hgram]
    exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by
    dsimp only [H]
    rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]
  let K : Mx D ρ ρ := w • H
  have hKint (m i : Fin ρ) : K m i ∈ intAt D (· = v) := by
    change (w • H) m i ∈ intAt D (· = v)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.IwaPlace.DualIso.intAt_mul_mem hw (hHint m i)
  let c'' : Mx D S.rank ρ := c' - c * K
  have hpair : adj c'' * (gA S * c) = ε • (1 : Mx D ρ ρ) := by
    dsimp only [c'']
    rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero,
      sub_zero, hcc]
  refine ⟨c'', ?_, hpair, ?_⟩
  · intro i
    have hcol : (fun k => (c * K) k i) = ∑ m, K m i • (fun k => c k m) := by
      funext k
      simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
    change (fun k => c' k i) - (fun k => (c * K) k i) ∈ M
    rw [hcol]
    exact sub_mem (hc' i) (AddSubgroup.sum_mem _ fun m _ =>
      GlobalTheory.IwaPlace.DualIso.smul_mem_of_isSDAt hM (hKint m i) (hc m))
  · have hleft : adj c'' * (gA S * c') = H - (ε * cA D w) • H := by
      dsimp only [c'']
      rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']
      change H - adj (w • H) * (ε • (1 : Mx D ρ ρ)) = _
      rw [adj_smul, hadjH, mul_smul_comm, mul_one, smul_smul]
    have hsum : ε * cA D w + ε * w = ε := by
      rw [← mul_add, add_comm, hwc, hεε]
    calc
      adj c'' * (gA S * c'') =
          adj c'' * (gA S * c') - (adj c'' * (gA S * c)) * K := by
        change adj c'' * (gA S * (c' - c * K)) = _
        rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
          ← Matrix.mul_assoc (adj c'') (gA S * c) K]
      _ = H - (ε * cA D w) • H - (ε * w) • H := by
        rw [hleft, hpair]
        change H - (ε * cA D w) • H - (ε • (1 : Mx D ρ ρ)) * (w • H) = _
        rw [smul_mul_assoc, one_mul, smul_smul]
      _ = 0 := by rw [sub_sub, ← add_smul, hsum, hεH, sub_self]
