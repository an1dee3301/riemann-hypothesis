module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMulInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondStd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.BinderNameHint
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.VacNonzeroReal

variable {D : D7}

theorem continuous_finTmul (e : D.host.E) :
    Continuous fun x : Af D.host.F => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x :=
    continuous_const.prodMk continuous_id
  have h2 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    h1.smul (continuous_const : Continuous fun _ : Af D.host.F => ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D))
  refine h2.congr fun x => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infPart_finTmul (x : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]

theorem finPart_infTmul (x : Ainf D.host.F) (e : D.host.E) :
    finPart D (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Af D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]


set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 1600000 in
theorem decomp_AE (V : AddSubgroup (AE D)) (hV : IsOpen (V : Set (AE D))) (z : AE D) :
    ∃ e : D.host.E, ∃ u ∈ V, infPart D u = 0 ∧ ∃ r : AE D, finPart D r = 0 ∧ z = incA D e + u + r := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, V.zero_mem, map_zero _, 0, map_zero _, by rw [map_zero, add_zero, add_zero]⟩
  | tmul a e =>
    set W : Set (Af D.host.F) := (fun x => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D)) ⁻¹' V with hW
    have hWo : IsOpen W := hV.preimage (continuous_finTmul e)
    have hO : IsOpen {x : Af D.host.F | a.2 - x ∈ W} := hWo.preimage (continuous_const.sub continuous_id)
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.CondStd.dense_F.exists_mem_open hO
      ⟨a.2, by
        show (pairA D.host.F 0 (a.2 - a.2) ⊗ₜ[D.host.F] e : AE D) ∈ V
        rw [sub_self]
        have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
        rw [this, TensorProduct.zero_tmul]
        exact V.zero_mem⟩
    refine ⟨algebraMap D.host.F D.host.E c * e, _, hc, infPart_finTmul _ _, _, finPart_infTmul (a.1 - algebraMap D.host.F (Ainf D.host.F) c) e, ?_⟩
    have hinc : incA D (algebraMap D.host.F D.host.E c * e) =
        algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e := by
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) = _
      have h1 : (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] algebraMap D.host.F D.host.E c) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h2 : algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e =
          (algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [h1, h2, ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
    rw [hinc, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show a.1 = algebraMap D.host.F (Ainf D.host.F) c + 0 + (a.1 - algebraMap D.host.F (Ainf D.host.F) c)
      abel
    · show a.2 = algebraMap D.host.F (Af D.host.F) c + (a.2 - algebraMap D.host.F (Af D.host.F) c) + 0
      abel
  | add x y hx hy =>
    obtain ⟨e, u, hu, hu0, r, hr0, hx⟩ := hx
    obtain ⟨e', u', hu', hu0', r', hr0', hy⟩ := hy
    refine ⟨e + e', u + u', V.add_mem hu hu', by rw [map_add (f := _), hu0, hu0', add_zero], r + r',
      by rw [map_add (f := _), hr0, hr0', add_zero], ?_⟩
    rw [hx, hy, map_add (f := _), add_add_add_comm _ r, add_add_add_comm (incA D e) u]

theorem continuous_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    Continuous fun v : AE D => (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply, and_self, if_true]
    exact continuous_id
  · have : ∀ v : AE D, (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) a b = 0 := fun v => by
      rw [Matrix.single_apply, if_neg h]
    simpa only [this] using continuous_const

def singleHom {m n : ℕ} (i : Fin m) (j : Fin n) : AE D →+ Matrix (Fin m) (Fin n) (AE D) where
  toFun v := Matrix.single i j v
  map_zero' := Matrix.single_zero i j
  map_add' x y := Matrix.single_add i j x y

theorem decomp_WO {S T : HSp D} (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) (w : WO S T) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ U, u.map (infPart D) = 0 ∧
      ∃ r : WO S T, r.map (finPart D) = 0 ∧ w = ratW T S γ + u + r := by
  classical
  have hV : ∀ i j, IsOpen ((U.comap (singleHom i j) : AddSubgroup (AE D)) : Set (AE D)) := fun i j =>
    hU.preimage (continuous_single i j)
  choose e u hu hu0 r hr0 hw using fun i j => decomp_AE _ (hV i j) (w i j)
  refine ⟨Matrix.of e, Matrix.of u, ?_, ?_, Matrix.of r, ?_, ?_⟩
  · rw [Matrix.matrix_eq_sum_single (Matrix.of u)]
    exact U.sum_mem fun i _ => U.sum_mem fun j _ => hu i j
  · ext i j
    simp [hu0 i j]
  · ext i j
    simp [hr0 i j]
  · ext i j
    rw [hw i j]
    rfl

theorem exists_finPart_zero_ne : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  intro D ψ θ S T sS sT LS LT f hv
  have hne := GlobalTheory.TwistFactorProof.vac_ne_zero hv
  have hth : IsThetaFunO ψ S T f := hv.2.theta
  obtain ⟨w0, hw0⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨U, hUo, hU⟩ := hth.level
  obtain ⟨γ, u, huU, hu0, r, hr0, rfl⟩ := decomp_WO U hUo w0
  refine ⟨r, hr0, fun hfr => ?_⟩
  have hψ : ∀ a, ψ a ≠ 0 := fun a => by
    have : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one this
  rw [add_assoc, hth.quasi γ (u + r)] at hw0
  have hfur : f (u + r) ≠ 0 := right_ne_zero_of_mul hw0
  have h2 := congrFun (hU u huU hu0) r
  unfold heisO at h2
  rw [hfr, add_comm r u] at h2
  exact (mul_ne_zero (hψ _) hfur) h2

end GlobalTheory.VacNonzeroReal
