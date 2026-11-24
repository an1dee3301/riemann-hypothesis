module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerSteps

variable {D : D7}

theorem hasInfQ_tauE {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
      ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm

theorem hasInfExp_mul_zero {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ 0) : HasInfExp D (χ * η) τ a := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  have hm0 : m = 0 := by exact_mod_cast hm.trans (mul_zero _)
  refine ⟨n, hn, h1, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h2 θ hθ x hx hτ, h3 θ hθ x hx hτ, hm0, zpow_zero, mul_one]



theorem sum_mul_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i ∈ s, p i * p i = p i)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0) {i : ι} (hi : i ∈ s) : p i * (∑ i ∈ s, p i) = p i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h0 i hi j hj hji) (fun h => absurd hi h), h i hi]

theorem resS_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hint, fun PP hP => ?_⟩
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 (hsum ▸ hc)
  have h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hcross i hi j hj) (hcross j hj i hi) hji
  have h3 : es PP * e = es PP := by
    rw [hsum]; exact sum_mul_idem (R := AE D) es P h1 h2 hP
  obtain ⟨h4, h5⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h6 : (⟨_, h4⟩ * ⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, h4⟩ :=
    Subtype.ext (by change toEAf D _ * toEAf D _ = toEAf D _; rw [← RingHom.map_mul, h3])
  have h7 := congrArg (resS D.host.F PP) h6
  rwa [map_mul, h5, one_mul] at h7









end GlobalTheory.InnerSteps

end
