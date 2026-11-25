module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
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
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace.CombAll

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_form (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {y : WO S T}
    (hy : IsHalf (cA D p.e) y) : ∃ b : Matrix Y Y' k, ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  set N : Matrix (Fin S.rank) (Fin T.rank) k := (y.map fun a => p.π (cA D a)).transpose with hN
  have hyN : y = N.transpose.map fun a => cA D (p.ι a) := by
    ext i j
    simp only [hN, Matrix.transpose_transpose, Matrix.map_apply, p.ι_π, map_mul, Formalism.L2.Theta.cA_cA]
    exact (hy i j).symm
  refine ⟨(FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β).transpose, fun t => ?_⟩
  rw [hyN, GlobalTheory.LocSympl.pi_hO_up]
  rw [show (S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ) =
      ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) * FS.γ by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  rw [show FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) =
      (FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β) * t by
    simp only [Matrix.mul_assoc]]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem exists_heis (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (O : SB (Matrix Y Y' k)) {u : WO S T}
    (hu : IsHalf (p.e + cA D p.e) u) :
    ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) := by
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  have h1 := p.split.1
  have h1' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, h1]
  set x := p.down FS FT u with hx
  set y : WO S T := cA D p.e • u with hyd
  have hy : IsHalf (cA D p.e) y := fun i j => by
    simp only [hyd, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1']
  have hux : p.up FS FT x = p.e • u := by
    rw [hx]
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact p.ι_π _
  have hsum : y + p.up FS FT x = u := by
    rw [hux]
    ext i j
    simp only [hyd, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, add_comm]
    exact hu i j
  obtain ⟨b, hb⟩ := exists_form p FS FT hy
  let Φx : SB (Matrix Y Y' k) := ⟨fun t => O.1 (t + x), GlobalTheory.LocComb.trans_mem_SB O.2 x⟩
  let Φm : SB (Matrix Y Y' k) := ⟨fun t => GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t, GlobalTheory.LocComb.modul_mem_SB hd Φx.2 b⟩
  refine ⟨ψ (-symplOH S T y (p.up FS FT x)) • Φm, fun Tm h => ?_⟩
  have e1 : Tm Φx = heisO ψ S T (p.up FS FT x) (Tm O) := h.trans x O Φx fun _ => rfl
  have e2 : Tm Φm = heisO ψ S T y (Tm Φx) := h.modul y hy Φx Φm fun t => by
    show GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t = _
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hψk t y, hb t]
    rfl
  have e3 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y (p.up FS FT x) (Tm O)
  change heisO ψ S T y (heisO ψ S T (p.up FS FT x) (Tm O)) =
    ψ (symplOH S T y (p.up FS FT x)) • heisO ψ S T (y + p.up FS FT x) (Tm O) at e3
  rw [map_smul, e2, e1, e3, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul, hsum]

end GlobalTheory.FlatPlace.CombAll

namespace GlobalTheory.FlatPlace

theorem isCombAt_of_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) → ∀ T₀, p.IsModel ψ FS FT T₀ → ∀ O Ξ : SB (Matrix Y Y' k), IsOne O → T₀ O ≠ 0 → T₀ Ξ = comb ψ S T c (T₀ O) → p.IsCombAt ψ FS FT c Ξ.1 := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT c hc T₀ hT₀ O Ξ hO hT₀O hΞ
  classical
  have hA : ∀ u : c.support, ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) :=
    fun u => CombAll.exists_heis p ψ hψ FS FT O (hc u u.2)
  choose Φ hΦ using hA
  let Ξ' : SB (Matrix Y Y' k) := ∑ u : c.support, c u • Φ u
  have hΞ' : ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ξ' = comb ψ S T c (Tm O) := fun Tm h => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Ξ', map_sum, map_smul, fun u => hΦ u Tm h]
    rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum]
    exact Finset.sum_coe_sort c.support (fun u => c u • heisO ψ S T u (Tm O))
  have hinj : Ξ = Ξ' := by
    by_contra hne
    have h0 : Ξ - Ξ' ≠ 0 := sub_ne_zero.2 hne
    have e1 : T₀ (Ξ - Ξ') = ((0 : ℂ) • T₀) (Ξ - Ξ') := by
      rw [map_sub, hΞ, hΞ' T₀ hT₀, sub_self, LinearMap.smul_apply, zero_smul]
    have e2 := (GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT ψ hψ).1 T₀ ((0 : ℂ) • T₀) hT₀
      (GlobalTheory.LocMod.Witness.isModel_smul p hT₀ 0) _ h0 e1
    apply hT₀O
    rw [e2, zero_smul, LinearMap.zero_apply]
  refine ⟨hc, fun Tm h Φ₀ Φ' h1 h2 => ?_⟩
  have e2 : Φ' = Ξ' := by rw [← hinj]; exact Subtype.ext h2
  have e3 : Φ₀ = O := Subtype.ext (h1.trans hO.symm)
  rw [e2, e3, hΞ' Tm h]

end GlobalTheory.FlatPlace
