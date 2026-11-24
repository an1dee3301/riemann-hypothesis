module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRepApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
noncomputable section

namespace GlobalTheory.ConjWeilBack

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7}

theorem key {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    GlobalTheory.AdjTr.conjRep ω p F = cj id ((ω.toSgn true) ((ofSgn true S).symm p.1, p.2) (cj id F)) := rfl

theorem actO_negS' (S T : HSp D) (g : GA D (negSp S)) (h : GA D T) (w : WO S T) :
    actO (negSp S) T g h w = actO S T (ofSgn true S g) h w := by
  unfold actO; rfl

theorem ofSgn_symm_mem_GQ (S : HSp D) (γ : GA D S) (h : γ ∈ GQ S) : (ofSgn true S).symm γ ∈ GQ (negSp S) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (GlobalTheory.ConjWeil.UJ_neg _ _)


open GlobalTheory.ConjWeil in
theorem weil_conjRep_of_neg : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S T), GlobalTheory.Grid.IsWeil ψ true S T χS χT ω → IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (GlobalTheory.AdjTr.conjRep ω) := by
  intro D ψ S T χS χT ω hw
  change IsWeilDatumO ψ (negSp S) T χS χT (ω.toSgn true) at hw
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f) := fun f => (I.1 f).2.symm
  have hz2 : ∀ (w : WO S T) (X : WO S T → ℂ), heisO ψ S T w (cj id X) = cj id (heisO ψ (negSp S) T w X) := fun w X => by
    have := congrArg (cj id) (I.2 w (cj id X)).2
    rw [cj_id_cj_id, cj_id_cj_id] at this
    exact this.symm
  have hz1 : ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ (negSp S) T w (cj id f) = cj id (heisO ψ S T w f) :=
    fun w f => (I.2 w f).2
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [key, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [key, key, ← hz1, hw.om_heis _ _ _ _ ((thS f).1 hf), hz2, actO_negS']
    rfl
  · intro γ hγ γ' hγ' f hf
    rw [key]
    show starRingEnd ℂ ((ω.toSgn true) ((ofSgn true S).symm γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (ofSgn_symm_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [key]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_ofSgn_symm true S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF ((ofSgn true S).symm p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [key, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he ((ofSgn true S).symm g) h
      (by unfold SuppAt; exact hg) hh x y (by unfold IsDetAt; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id ((ω.toSgn true) ((ofSgn true S).symm g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← hz2, hℓ u hu (cj id f') ((thS (cj id f')).2 (by rwa [cj_id_cj_id]))]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← key ω (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

end GlobalTheory.ConjWeilBack
