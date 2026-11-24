module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
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
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
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
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.LocMod.Witness

theorem exists_isModel_of_isThetaAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  classical
  intro D k _ _ _ _ p ψ hψ S T ΛS ΛT hS hT Y Y' _ _ _ _ FS FT hlat f₀ φ f hf₀ hφ hθ
  obtain ⟨⟨T₀, h₀⟩, hall⟩ := hθ
  have hf : f = T₀ φ := hall T₀ h₀

  have hNk : ∀ N : ℕ, 0 < N → (N : k) ≠ 0 := fun N hN h => by
    have h1 : prH p (N : D.host.E) = 0 := by rw [map_natCast]; exact h
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact h2 ((map_eq_zero (prH p)).1 h1)
  obtain ⟨N, hN, hinv, hsupp⟩ := hφ.2
  have hN0 := hNk N hN
  have hA := lat_compact p FS FT hS hT
  have hAo := lat_open p FS FT hS hT
  generalize hAd : ((latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True).comap (upH p FS FT) : AddSubgroup _) = A at hA hAo
  have memA : ∀ x, x ∈ A ↔ p.up FS FT x ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := fun x => by
    rw [← hAd]; rfl
  have hup_smul : ∀ x : Matrix Y Y' k, p.up FS FT (N • x) = N • p.up FS FT x := fun x => map_nsmul (upH p FS FT) N x
  have hNx : ∀ x : Matrix Y Y' k, (N : k) • x = N • x := fun x => Nat.cast_smul_eq_nsmul k N x

  let g : Matrix Y Y' k → ℂ := fun x => φ (p.up FS FT x)
  have hlc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : IsOpen ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) :=
      hAo.preimage ((continuous_const_smul ((N : k)⁻¹)).comp (continuous_id.sub continuous_const))
    have hx : x ∈ ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) := by
      simp only [Set.mem_preimage, sub_self, smul_zero]; exact A.zero_mem
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy' : (N : k)⁻¹ • (y - x) ∈ A := hy
    have e1 : y = x + N • ((N : k)⁻¹ • (y - x)) := by
      rw [← hNx, smul_smul, mul_inv_cancel₀ hN0, one_smul, add_sub_cancel]
    change φ (p.up FS FT y) = φ (p.up FS FT x)
    rw [e1, up_add, hup_smul]
    exact hinv _ ((memA _).1 hy') (up_half p FS FT _) _
  have hcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (hA.image (continuous_const_smul (N : k)⁻¹)) fun x hx => ?_
    by_contra h
    apply hx
    have h1 := hsupp _ h
    rw [← hup_smul, ← memA] at h1
    refine ⟨N • x, h1, ?_⟩
    change (N : k)⁻¹ • (N • x) = x
    rw [← hNx, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let Φ : SB (Matrix Y Y' k) := ⟨g, hlc, hcs⟩

  have hext : ∀ Ψ : SB (Matrix Y Y' k), IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (ext p FS FT Ψ) :=
    ext_sb p FS FT hS hT
  refine ⟨T₀.comp (ext p FS FT), ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun O hO => ?_, Φ, fun x => rfl, ?_⟩
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T _ _ hS hT p.e p.split.1 (GlobalTheory.PlaceCoord.infPart_split p.split)
      _ hf₀ T₀ h₀ _ (hext Ψ)
  · refine Eq.trans (congrArg T₀ ?_) (h₀.trans _ (hext Ψ) _ (up_half p FS FT x))
    funext t
    rw [ext_apply, ext_apply, down_add, down_up, h]
    exact if_congr (half_add (up_half p FS FT x)).symm rfl rfl
  · refine Eq.trans (congrArg T₀ ?_) (h₀.modul _ (hext Ψ) _ hy)
    funext t
    rw [ext_apply, ext_apply, h]
    split_ifs with ht
    · rw [up_down p FS FT ht]
    · rw [mul_zero]
  · have e1 : ext p FS FT O = (1 : ℂ) • halfInd p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := by
      funext t
      rw [one_smul, ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht, hO, Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        rw [and_iff_left ht, ← up_down p FS FT ht, down_up, hlat]
        rfl
      · rw [if_neg ht, if_neg fun h => ht h.2]
    change T₀ (ext p FS FT O) = f₀
    rw [e1]
    exact h₀.vac
  · change T₀ (ext p FS FT Φ) = f
    rw [hf]
    congr 1
    funext t
    rw [ext_apply]
    split_ifs with ht
    · change φ (p.up FS FT (p.down FS FT t)) = φ t
      rw [up_down p FS FT ht]
    · by_contra h
      exact ht (hφ.1 t (Ne.symm h))

end GlobalTheory.LocMod.Witness
