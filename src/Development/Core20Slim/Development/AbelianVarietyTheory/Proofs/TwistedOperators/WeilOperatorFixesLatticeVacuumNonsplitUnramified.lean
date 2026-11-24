module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQuaStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
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
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertVac

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem placeIdem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := GlobalTheory.SplitIdem.af_ext _ fun w => by
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h']
  | neg x _ h => rw [smul_neg, h]

theorem mem_latO_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u :=
  ⟨fun h => ⟨GlobalTheory.PlaceModel.latO_le_top _ h, placeIdem_smul_eq hε h⟩,
    fun h => h.2 ▸ GlobalTheory.PlaceModel.placeIdem_smul_mem hε h.1⟩

theorem actO_inv_actO (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  unfold actO
  rw [inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← GlobalTheory.FinWeilO.mt_mul, inv_mul_cancel,
    GlobalTheory.FinWeilO.mt_one, Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.FinWeilO.mt_mul, inv_mul_cancel,
    GlobalTheory.FinWeilO.mt_one, Matrix.one_mul]

theorem actO_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) :=
  Function.LeftInverse.injective (actO_inv_actO g h)

theorem om_fixes_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ (g : GA D S) (h : GA D T), SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → om (g, h) f₀ = f₀ := by
  intro D ψ S T χS χT om hW ΛS ΛT hS hT v ε hv uS uT g h hg hh hst f₀ hf hvac
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv uS uT g h hg hh
    (fun u => ?_) f₀ hf fun u hu => ?_
  · rw [mem_latO_place_iff hv.1, mem_latO_place_iff hv.1, ← hst, ← GlobalTheory.FinWeilO.actO_smul,
      (actO_injective g h).eq_iff]
  · obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, placeIdem_smul_eq hv.1 hu]
    have h2 := hvac.1 (a • u)
      (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
    rwa [h1] at h2

end GlobalTheory.InertVac

end
