module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

namespace I195MixedCoordinates_16b53debd46a2c18720dfcab

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_16b53debd46a2c18720dfcab

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

variable {D : D7}

theorem isIsoSplit_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hq : d.qX * d.e = 1 := d.e'e
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm⟩
  · exact Matrix.mulVec_injective_iff.1 fun x y h => by
      have := congrArg (d.qX *ᵥ ·) h
      simpa only [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec] using this
  · rw [cT_sig]; exact d.ee
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]; exact d.iso
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig]
    apply rat_injective
    rw [rat_mul, rat_mul, rat_conjTranspose, rat_zero, Matrix.mul_assoc]
    exact d.wittDecomp_gram_X_anisotropic

set_option maxHeartbeats 1000000 in
theorem mem_NI_hyp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S) (h1 : mt S g ⬝ d.jX = d.jX)
    (h2 : d.pY ⬝ mt S g = d.pY) (B : Mx D ρ S₀.rank) (h3 : mt S g ⬝ d.j0 = d.j0 + d.jX ⬝ B) : g ∈ NI S d.e := by
  apply Subgroup.subset_closure
  have hm1 : (mt S g - 1) ⬝ d.jX = 0 := by rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  have hm0 : (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B := by rw [Matrix.sub_mul, h3, Matrix.one_mul, add_sub_cancel_left]
  refine ⟨hm1, ?_, ?_⟩
  · rw [cT_sig]
    change d.pY ⬝ (mt S g - 1) = 0
    rw [Matrix.mul_sub, h2, Matrix.mul_one, sub_self]
  · intro x hx
    rw [cT_sig] at hx
    refine ⟨B *ᵥ (d.p0 *ᵥ fun i => incA D (x i)), ?_⟩
    have hv : d.pY *ᵥ (fun i => incA D (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec (incA D) d.qY x i
      change incA D (((d.eᴴ * HSpace.gram S) *ᵥ x) i) = _ at this
      rw [hx, Pi.zero_apply, map_zero] at this
      exact this.symm
    have hsum : (fun i => incA D (x i)) = d.jX *ᵥ (d.pX *ᵥ fun i => incA D (x i)) +
        d.j0 *ᵥ (d.p0 *ᵥ fun i => incA D (x i)) := by
      have h := congrArg (· *ᵥ fun i => incA D (x i)) d.sum_eq_one
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero] at h
      exact h.symm
    have hX : ∀ a, mt S g *ᵥ (d.jX *ᵥ a) = d.jX *ᵥ a := fun a => by rw [Matrix.mulVec_mulVec, h1]
    have h0 : ∀ a, mt S g *ᵥ (d.j0 *ᵥ a) = d.j0 *ᵥ a + d.jX *ᵥ (B *ᵥ a) := fun a => by
      rw [Matrix.mulVec_mulVec, h3, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    have final : (mt S g - 1) *ᵥ (fun i => incA D (x i)) = d.jX *ᵥ (B *ᵥ (d.p0 *ᵥ fun i => incA D (x i))) := by
      have hs := Matrix.sub_mulVec (mt S g) (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (fun i => incA D (x i))
      rw [Matrix.one_mulVec] at hs
      rw [hs]
      conv_lhs => rw [hsum]
      rw [Matrix.mulVec_add, hX, h0]
      abel
    exact final

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge
open GlobalTheory.MixModel
variable {D : D7}

theorem orthProjPartHomToHermitian_eq_wittDecompositionCore {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w : WO S₀ T) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w := by
  rw [HypDec.matrixExtendByZero_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, cT_sig, Matrix.mul_assoc]
  rfl

theorem integrand_eq {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (x a : Mx D T.rank ρ) (w : WO S₀ T) :
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 =
      heisO ψ S T (d.extX T x) f (d.extY T a + d.ext0 T w) := by
  rw [d.integrandS_eq]
  simp only [heisO]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extX T x) (d.ext0 T w), d.wittDecomp_sympl_extIsotropic_extAnisotropic T x w,
    neg_zero, add_zero, add_right_comm]

theorem mixS_eq_res {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f) := by
  funext w
  simp only [_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, orthProjPartHomToHermitian_eq_wittDecompositionCore]
  congr 1
  funext a
  exact integrand_eq d ψ f x a w

theorem mixS_heis {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 := by
  funext w
  simp only [_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source]
  congr 1
  funext a
  change heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 =
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T 0) (heisO ψ S T (d.ext0 T w) (heisO ψ S T (d.extX T x) f))) 0
  rw [integrand_eq d ψ f x a w, integrand_eq d ψ _ 0 a w, map_zero]
  simp only [heisO, add_zero, GlobalTheory.OrientedHeis.symplOH_add_left]
  rw [symplOH_skew S T 0 (d.extY T a), symplOH_skew S T 0 (d.ext0 T w)]
  simp only [symplOH_zero_left, neg_zero, zero_add, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Bridge

namespace GlobalTheory.Bridge

open GlobalTheory.MixModel

theorem heis_bridge : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (0 < ρ → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀) ∧ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ = ratMx D T.rank ρ ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e y = d.extY T y) ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e' y = d.extX T y) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w) ∧ (∀ μ 𝓕 f x, (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f)) ∧ (∀ μ 𝓕 f x, (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 f x = (_root_.I195MixedCoordinates_16b53debd46a2c18720dfcab.source d) T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0) ∧ (∀ b, d.nB b ∈ NI S d.e) ∧ ∀ c, d.nC c ∈ NI S d.e := by
  intro D ψ S S₀ T ρ d
  exact ⟨isIsoSplit_hyp d, rfl, fun _ => rfl, fun _ => rfl, orthProjPartHomToHermitian_eq_wittDecompositionCore d T,
    fun μ 𝓕 f x => mixS_eq_res d ψ μ 𝓕 f x, fun μ 𝓕 f x => mixS_heis d ψ μ 𝓕 f x,
    fun b => mem_NI_hyp d _ (d.nB_jX b) (d.pY_nB b) b (d.nB_j0 b),
    fun c => mem_NI_hyp d _ (d.nC_jX c) (d.pY_nC c) 0 (by rw [d.nC_j0, Matrix.mul_zero, add_zero])⟩

end GlobalTheory.Bridge

end
