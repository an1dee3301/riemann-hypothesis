module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem nuH_not_unrAt_above {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) ∈ G.pl.S0) : ¬ (nuH G t i j).UnrAt P := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [← div_eq_mul_inv, nuH, div_div_cancel]
  intro hn
  rcases G.pl.mem_S0_of_sum_eq.1 hP with hv | hv
  · have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      rw [hv] at h
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt P := by
      by_contra hc
      rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h hv
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
    apply (G.ch.lev0 _ hm.1 hm.2 _ hv).2
    rw [e]
    exact (hmu.mul hxi).mul hn.inv
  · apply (G.ch.lev1 _ hm.1 hm.2 P hv).2
    rw [e]
    exact (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame P) (hL.xi_tame t P)).mul (hn.levelLe 1).inv

theorem heckeL_eq_of_ram {K : Type} [Field K] [NumberField K] {χ : HChar K} {S : Set (HeightOneSpectrum (𝓞 K))}
    (hr : ∀ w ∈ S, ¬ χ.UnrAt w) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 < s.re) :
    GlobalTheory.LFun.heckeL S χ s = Λ s := by
  have e : ({w | w ∉ S} : Set (HeightOneSpectrum (𝓞 K))).mulIndicator (GlobalTheory.CMVal.eulerFactor χ s) =
      GlobalTheory.CMVal.eulerFactor χ s :=
    Set.mulIndicator_eq_self.2 fun w hw => by
      by_contra h
      exact hw (if_neg (hr w (not_not.1 h)))
  have h := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ S}) (f := GlobalTheory.CMVal.eulerFactor χ s)).2
    (by rw [e]; exact hΛ.2 s hs)
  unfold GlobalTheory.LFun.heckeL GlobalTheory.LFun.eulerProd
  simp only [GlobalTheory.LFun.locL_heckeFam]
  exact h.tprod_eq

theorem chs_nu (G : GridData L sc) (i j : Fin D.R.m) (t : T) : (chs G i j t).ν = G.nu t i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem charL_chs_eq : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G i j t s Λ hs hΛ => ?_⟩⟩
  rw [chs_nu, GlobalTheory.LFun.charL_eq_of_chrEq (chrEq_nu G t i j hL)]
  refine heckeL_eq_of_ram (fun w hw => nuH_not_unrAt_above hL G t i j w hw) hΛ ?_
  rw [Complex.natCast_re]
  exact_mod_cast (by omega : 1 < s)

end GlobalTheory.SqStep
