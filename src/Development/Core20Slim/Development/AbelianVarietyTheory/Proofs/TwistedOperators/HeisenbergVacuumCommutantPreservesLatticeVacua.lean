module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

noncomputable section

namespace GlobalTheory.Asc

variable {D : D7}

theorem symplOH_swap {S T : HSp D} (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  have h := symplOH_self (S := S) (T := T) (x + y)
  rw [symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_self, symplOH_self] at h
  linear_combination h

theorem symplO_swap {S T : HSp D} (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap]; ring

theorem psi_symplO_swap (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x y : WO S T) :
    ψ (symplO S T y x) = 1 ↔ ψ (symplO S T x y) = 1 := by
  rw [symplO_swap, AddChar.map_neg_eq_inv, inv_eq_one]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a b : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T a (heisO ψ S T b f) = ψ (symplO S T a b) • heisO ψ S T b (heisO ψ S T a f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm b a, ← AddChar.map_add_eq_mul,
    GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap a b]
  have e : symplOH S T a b + symplOH S T a b + -symplOH S T a b = symplOH S T a b := by ring
  rw [e]

theorem annVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)),
    (∀ f, VacG ψ S T Γ f → ∀ w ∈ Ann ψ S T Γ, VacG ψ S T Γ (heisO ψ S T w f)) ∧
    (∀ w : WO S T, (∀ u ∈ Γ, u.map (infPart D) = 0) → w.map (finPart D) = 0 → w ∈ Ann ψ S T Γ) ∧
    ∀ (v : VolM D T.rank S.rank) f f₀, VacG ψ S T Γ f → VacG ψ S T Γ f₀ → ∀ w, w ∉ Ann ψ S T Γ →
      thPair v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
  intro D ψ hψ S T Γ
  refine ⟨fun f hf w hw => ?_, fun w hΓ hw => ?_, fun v f f₀ hf hf₀ w hw => ?_⟩
  · refine ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf.1 w, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · show heisO ψ S T (2 • u) (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.1 u hu, (psi_symplO_swap ψ _ _).2 (hw.1 u hu), one_smul]
    · show heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.2 e he u hu hh, (psi_symplO_swap ψ _ _).2 (hw.2 e he u hu hh), one_smul]
  · have key : ∀ u ∈ Γ, symplO S T w u = 0 := fun u hu => by
      rw [GlobalTheory.ThetaSquare.symplO_eq, (symplOH_fin_real (hΓ u hu) hw).2, add_zero]
    refine ⟨fun u hu => ?_, fun e _ u hu _ => by rw [key u hu, AddChar.map_zero_eq_one]⟩
    rw [key _ (Γ.nsmul_mem hu 2), AddChar.map_zero_eq_one]
  · obtain ⟨hμ, h𝓕, -⟩ := v.covol
    have hex : ∃ u, heisO ψ S T u f = f ∧ heisO ψ S T u f₀ = f₀ ∧ ψ (symplO S T w u) ≠ 1 := by
      by_contra hno
      push_neg at hno
      exact hw ⟨fun u hu => hno _ (hf.2.1 u hu) (hf₀.2.1 u hu),
        fun e he u hu hh => hno _ (hf.2.2 e he u hu hh) (hf₀.2.2 e he u hu hh)⟩
    obtain ⟨u, hu, hu₀, hc⟩ := hex
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀.1 w
    have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf.1 hg u
    rw [hu, heisO_comm, hu₀] at e1
    have e2 : GlobalTheory.Ker.ipO v.μ v.𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
        starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) := by
      unfold GlobalTheory.Ker.ipO
      rw [← integral_const_mul]
      congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
    have hc' : starRingEnd ℂ (ψ (symplO S T u w)) ≠ 1 := by
      intro h
      apply hc
      have h2 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, map_one] at h2
      exact (psi_symplO_swap ψ _ _).1 h2
    rw [e2] at e1
    show GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0
    have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
      linear_combination e1
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc')

end GlobalTheory.Asc

end
