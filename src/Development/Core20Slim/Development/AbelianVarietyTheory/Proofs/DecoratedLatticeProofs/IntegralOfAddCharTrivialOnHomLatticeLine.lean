module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvLat

open GlobalTheory.FinPl.SuppShift

variable {D : D7}

theorem single_mul_mul_single {ρ : ℕ} (M : Mx D ρ ρ) (i : Fin ρ) :
    (Matrix.single i i 1 : Mx D ρ ρ) ⬝ (M ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) = Matrix.single i i (M i i) := by
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one]

theorem pairS_single {W W₀ : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (i : Fin ρ) (c : AE D) (x : Mx D W.rank ρ) :
    pairS W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) x = cA D ((dW.pY ⬝ x) i i) * c := by
  have h : adj (dW.pY ⬝ x) = adj x ⬝ (gA W ⬝ dW.jX) := by
    rw [dW.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  rw [pairS, ← Matrix.mul_assoc (gA W), ← Matrix.mul_assoc, ← h, Matrix.trace_mul_single, op_smul_eq_mul]
  rfl


set_option maxHeartbeats 1600000 in
theorem int_of_psi_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i : Fin ρ) (c : AE D), c - 1 ∈ idAt D (· = v) → (∀ b ∈ idAt D (· = v), dV.extY W (dW.jY ⬝ Matrix.single i i b) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) → ψ (symplO V W (dV.extX W (dW.jX ⬝ Matrix.single i i c)) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) = 1) → c - 1 ∈ intAt D (· = v) := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hV hW hmV hmW hcols i c hc1 hyp
  have hU : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) ∈
      latO V W (LV : Set _) (LW : Set _) (· = v) := by
    refine (SelfDualAt.latO_ann_at D ψ hψ V W LV LW hV hW (· = v) _ fun k l => ?_).2 fun u hu => ?_
    · rw [Matrix.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (eps_idAt v)
    have hux := LatMem.latO_mxAt hu
    have hfixu : SelfDualAt.cP (· = v) • u = u := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      exact eps_mul (hux k l)
    have hπ := sandwich_latO hV hW (dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmW z).1 hz).2.1 i)
      (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmV z).1 hz).2.1 i) hu
    have e : dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY ⬝ (u ⬝ (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY)) =
        dV.extY W (dW.jY ⬝ (Matrix.single i i ((dW.pY ⬝ (u ⬝ dV.jY)) i i) : Mx D ρ ρ)) := by
      rw [HypDec.extY_apply, ← single_mul_mul_single]
      simp only [Matrix.mul_assoc]
    rw [e] at hπ
    have h1 := hyp _ (mxAt_mul_left dW.pY (mxAt_mul_right hux dV.jY) i i) hπ
    rw [symplO_eq, hO_extX, pairS_single, HypDec.extY_apply, Matrix.mul_assoc, dV.pY_jY, Matrix.mul_one,
      ← Matrix.mul_assoc dW.pY dW.jY, dW.pY_jY, Matrix.one_mul, Matrix.single_apply_same] at h1
    rw [← SelfDualAt.symplO_smul_swap, hfixu, symplO_eq, hO_extX, pairS_single]
    exact h1
  have hint : finPart D c ∈ intAE D := by
    refine int_of_stable dV hV hmV i hc1 fun a ha => ?_
    have ha' := idAt_of_colMul dV ha
    have h := LatMem.latO_maps hV hU ha
    have e : (SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ))) *ᵥ colMul dV.jX i a =
        colMul dW.jX i (c * a) := by
      have e0 : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) =
          eps v • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) := by
        ext k l
        rw [Matrix.smul_apply, Algebra.smul_def]
        rfl
      rw [e0, Matrix.smul_mulVec, HypDec.extX_apply, ← Matrix.mulVec_mulVec, single_mulVec', pX_colMul,
        ← colMul_mul, eps_mul (Ideal.mul_mem_left _ _ ha')]
    rw [e] at h
    exact (hcols i _ (Ideal.mul_mem_left _ _ ha')).2 h
  refine ⟨hc1, ?_⟩
  rw [RingHom.map_sub]
  exact sub_mem hint (int_of_idem (one_mul 1))

end GlobalTheory.FinPl.InvLat
