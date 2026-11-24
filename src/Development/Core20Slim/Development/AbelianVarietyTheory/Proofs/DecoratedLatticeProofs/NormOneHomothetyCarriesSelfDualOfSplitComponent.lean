module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
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
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat


set_option maxHeartbeats 1000000 in
theorem sMoves_of_wComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (L L' : Lat S) (c : AE D) (g : GA D S), IsSelfDualC S L → IsSelfDualC S L' → NormOneAt p.v c → (∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ latV S L (· = p.v) ↔ (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i)) ∈ latV S L' (· = p.v)) → SMoves S c g L L' p.v := by
  intro D k _ _ _ _ p S L L' c g hL hL' hc hw
  have hpc : p.pr c * p.pr (cA D c) = 1 := by rw [← map_mul, hc.1, map_one]
  have hGinv : ∀ x : Fin S.rank → k,
      (Formalism.L2.Theta.mt S g).map p.pr *ᵥ ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      show Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = Formalism.L2.Theta.mt S (g * g⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.map_one p.pr (map_zero _) (map_one _), Matrix.one_mulVec]
  have hsec : ∀ u : Fin S.rank → k, Formalism.L2.Theta.mt S g *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) := by
    intro u
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have hc1 : ∀ a : k, c * p.sec a = p.sec (p.pr c * a) := by
    intro a; rw [mul_comm, sec_mul_right, mul_comm]
  have hc2 : ∀ b : k, c * cA D (p.sec b) = cA D (p.sec (p.pr (cA D c) * b)) := by
    intro b
    have h : c * cA D (p.sec b) = cA D (cA D c * p.sec b) := by rw [map_mul, cA_cA]
    rw [h, mul_comm, sec_mul_right, mul_comm]
  have hB : ∀ x z : Fin S.rank → k,
      ∑ i, ∑ j, (p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i * p.pr (cA D (incA D (S.gram i j))) *
          (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
    intro x z
    rw [← pairing_inv (p := p) g x z]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
      (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z) j)) * hpc
  intro y hy
  have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    simp only [Pi.add_apply, p.sec_pr]
    rw [map_mul, cA_cA, ← add_mul]
    exact ((idem_iff p _).1 (hy i)).symm
  obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
    ⟨_, _, hyd⟩
  have himg : c • (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) =
      (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u)) i)) +
        (fun i => cA D (p.sec ((p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) i))) := by
    funext i
    have h1 := congrFun (hsec u) i
    have h2 := congrFun (mt_csec (p := p) g z) i
    have h3 : (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i =
        p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [Matrix.mulVec_add, Pi.add_apply, h1, h2]
    have h4 : c * (p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i))) =
        p.sec (p.pr c * ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec (p.pr (cA D c) * (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [mul_add, hc1, hc2]
    show c * (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i = _
    refine (congrArg (c * ·) h3).trans (h4.trans ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [himg, decomp hL, decomp hL']
  refine and_congr (hw u) ?_
  rw [csec_mem_iff hL, csec_mem_iff hL']
  constructor
  · intro h x' hx'
    have hx : p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ
        (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))) = x' := by
      rw [Matrix.mulVec_smul, smul_smul, hpc, one_smul, hGinv]
    have hmem := (hw (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))).2 (by rw [hx]; exact hx')
    rw [← hx, hB]
    exact h _ hmem
  · intro h x hx
    have h5 := h _ ((hw x).1 hx)
    rwa [hB] at h5

end GlobalTheory.Core.Mi.LatMatch

end
