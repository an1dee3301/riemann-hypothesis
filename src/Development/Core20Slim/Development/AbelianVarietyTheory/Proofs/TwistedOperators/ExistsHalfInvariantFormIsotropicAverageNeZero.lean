module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConstStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticRestrictionIsotropicPartEqPairingStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroupStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparateStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
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
public import Init.BinderNameHint
public import Init.Classical
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
variable {D : D7}

theorem res_smul_twisted_operators {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (a : ℂ) (F : WO V W → ℂ) : res V V' W C B μ 𝓨 (a • F) = a • res V V' W C B μ 𝓨 F :=
  funext fun x => integral_const_mul a _

set_option maxHeartbeats 1000000 in
theorem avgForm_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∃ ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO V' W, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ V' W f → ℓ' (heisO ψ V' W u f) = ℓ' f) ∧ ∃ f, IsThetaFunO ψ V W f ∧ avgForm ψ V V' W C B μ 𝓨 K e ℓ' f ≠ 0 := by
  intro D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he
  have hR := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ
  have hth : ∀ {f : WO V W → ℂ}, IsThetaFunO ψ V W f → ∀ u, IsThetaFunO ψ V W (heisO ψ V W u f) :=
    fun hf u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  obtain ⟨f₁, hf₁, hres₁⟩ := hR.2
  obtain ⟨ℓ', hℓ', s, hs', hℓs⟩ : ∃ ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ, (∀ u, IsHalf (cA D e) u → ∀ f,
      IsThetaFunO ψ V' W f → ℓ' (heisO ψ V' W u f) = ℓ' f) ∧
      ∃ s, IsHalf e s ∧ ℓ' (heisO ψ V' W s (res V V' W C B μ 𝓨 f₁)) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hres₁ (GlobalTheory.ThetaStalk.eq_zero_of_invariant_forms D ψ hψ V' W e he _ (hR.1 f₁ hf₁).2.1 h)
  have hf₂ : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B s) f₁) := hth hf₁ _
  have h0 : ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B s) f₁)) ≠ 0 := by
    rw [(hR.1 f₁ hf₁).2.2.1 s]; exact hℓs
  refine ⟨ℓ', fun u hu f hf => hℓ' u hu f hf, ?_⟩
  by_contra hall
  push_neg at hall
  obtain ⟨L, Kc, hL, hKc, hz, hloc⟩ := GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he _ hf₂
  obtain ⟨L', hL', hL'L, hsep⟩ := GlobalTheory.T.exists_open_subgroup_half_characters_separate D ψ hψ W r e he L hL
  have hφ := GlobalTheory.T.eq_zero_of_integral_char_eq_zero_of_periodic_open (haarHalf (cA D e) W.rank r)
    (fun (a : halfMx e W.rank r) (t : halfMx (cA D e) W.rank r) => ψ (halfSympl W (a : Mx D W.rank r) (t : Mx D W.rank r)))
    (fun a s t => by simp only [AddSubgroup.coe_add, halfSympl_add_right, AddChar.map_add_eq_mul])
    (fun a => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_right, AddChar.map_zero_eq_one])
    (fun t => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_left, AddChar.map_zero_eq_one])
    (fun a b t => by simp only [AddSubgroup.coe_add, halfSympl_add_left, AddChar.map_add_eq_mul])
    L' hL' hsep
    (fun t => ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) (heisO ψ V W (midPart V V' W B s) f₁))))
    Kc hKc (fun t ht => by simp only [hz t ht, map_zero])
    (fun t l hl => by simp only [hloc t l (hL'L hl)])
    (fun a _ => by
      rw [← hall _ (hth hf₂ (isoPart V W C (a : Mx D W.rank r)))]
      unfold avgForm
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [GlobalTheory.ThetaStalk.heisO_comm (restEmb V W K (t : Mx D W.rank r)) (isoPart V W C (a : Mx D W.rank r)), res_smul_twisted_operators, map_smul, smul_eq_mul,
        (hR.1 _ (hth hf₂ _)).2.2.2 (a : Mx D W.rank r), GlobalTheory.T.symplectic_restriction_isotropic_part_eq_pairing D V V' W r C B hs K hKC])
  apply h0
  have := congrFun hφ 0
  simpa [restEmb, GlobalTheory.SplitScalar.heisO_zero] using this

end GlobalTheory.HalfAverage
