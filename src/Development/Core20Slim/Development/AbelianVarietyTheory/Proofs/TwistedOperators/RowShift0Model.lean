module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiArrowPairMovesStandardVacuumByScalar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPt0InvMemStdLatIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.LastVertexMove GlobalTheory.LastVertexInv GlobalTheory.FirstRowVertex

namespace GlobalTheory.FirstRowShift

private theorem locPl_under_mem_S0_or_Q {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  classical
  intro w hw
  rcases Finset.mem_union.mp hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    left
    rw [G.pl.w_over v hv]
    exact hv
  · exact Or.inr ⟨w, h, rfl⟩

private theorem isSBHalf_of_half_mem_iff {D : D7} {A B : HSp D} {e : AE D} {Λ Λ' : AddSubgroup (WO A B)}
    (hΛ : ∀ x, IsHalf e x → (x ∈ Λ ↔ x ∈ Λ')) {Φ : WO A B → ℂ} (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ' Φ := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  refine ⟨h1, k, hk, fun u hu hue t => h2 u ((hΛ u hue).mpr hu) hue t, fun t ht => ?_⟩
  exact (hΛ _ (GlobalTheory.StdHalfLat.half_nsmul (h1 t ht) k)).mp (h3 t ht)

theorem sb_std_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {e : AE D}, t ∈ U → IsIdemSum e (locPl G t) → ∀ i : Fin D.R.m,
    ∀ Φ : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ,
      IsSBHalf e (latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (G.latS (.chi i D.R.m : Pair T) : Set _) (G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) Φ →
      IsSBHalf e (stdLat S (.chi i D.R.m)) Φ := by
  intro D T L sc G W U S t e ht he i Φ hΦ
  have hS : DefNode D.R.m (Node.grid ((i : ℕ) + 1) D.R.m) := ⟨i.isLt, rfl⟩
  have hT : DefNode D.R.m (Node.grid (i : ℕ) D.R.m) := ⟨i.isLt.le, rfl⟩
  obtain ⟨a, ha, hga⟩ := GlobalTheory.StdHalfLat.exists_kill S.N ht
    (FinDatum.ind G t (Pair.chi (i : ℕ) D.R.m) (locPl G t) (locPl_under_mem_S0_or_Q G t) e he) hS
  obtain ⟨b, hb, hgb⟩ := GlobalTheory.StdHalfLat.exists_kill S.N ht
    (FinDatum.ind G t (Pair.chi (i : ℕ) D.R.m) (locPl G t) (locPl_under_mem_S0_or_Q G t) e he) hT
  have ha' : e * (a + cA D a) = 0 := ha
  have hb' : e * (b + cA D b) = 0 := hb
  obtain ⟨hS1, hS2⟩ := GlobalTheory.StdHalfLat.hat_moves S.N hS
  obtain ⟨hT1, hT2⟩ := GlobalTheory.StdHalfLat.hat_moves S.N hT
  have hga' : SuppAt a (G.pS (Pair.chi (i : ℕ) D.R.m)) (negGA _ (S.N.u (Node.grid ((i : ℕ) + 1) D.R.m)).1) := by
    unfold SuppAt
    rw [mt_negGA]
    exact hga
  unfold GlobalTheory.LastVertexMove.stdLat
  refine isSBHalf_of_half_mem_iff (fun x hx => ?_) hΦ
  refine (GlobalTheory.StdHalfLat.mem_latO_iff_of_half (S := G.pS (Pair.chi (i : ℕ) D.R.m)) (T := G.pT (Pair.chi (i : ℕ) D.R.m))
    (negGA _ (S.N.u (Node.grid ((i : ℕ) + 1) D.R.m)).1) (S.N.u (Node.grid (i : ℕ) D.R.m)).1
    (fun v hv => ?_) (fun v hv => ?_) hT1 hT2 ha' hb' hga' hgb hx).symm
  · rw [mt_negGA]
    exact hS1 v hv
  · rw [← map_inv (negGA (G.V (Node.grid ((i : ℕ) + 1) D.R.m))), mt_negGA]
    exact hS2 v hv

theorem actO_inv_actO {D : D7} {A B : HSp D} (g : GA D A) (h : GA D B) (u : WO A B) :
    actO A B g⁻¹ h⁻¹ (actO A B g h u) = u := by
  rw [← GlobalTheory.SplitLinear.actO_mul, inv_mul_cancel, inv_mul_cancel]
  simp [actO]

theorem vac_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m)),
    (∀ x : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)), actO _ _ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) ↔ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T)) →
    ∃ c : ℂ, W.om (.chi (firstIx D) D.R.m : Pair T) (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1) (S.Z.vac (.chi (firstIx D) D.R.m : Pair T)) = c • S.Z.vac (.chi (firstIx D) D.R.m : Pair T) := by
  intro D T L sc G W U S k hlat
  refine GlobalTheory.RowChiVac.vac_chi_scalar S (i := ((firstIx D : Fin D.R.m) : ℕ)) (firstIx D).isLt _ 1 ?_
  intro u
  have h := hlat (actO _ _
    (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1
    (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2 u)
  rw [actO_inv_actO] at h
  exact h

end GlobalTheory.FirstRowShift


open GlobalTheory.FirstRowShift in
theorem GlobalTheory.FirstRowShift.rowShift0_model : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T} {e : AE D},
    t ∈ U → IsIdemSum e (locPl G t) →
    ∀ k : FinPt G (.grid 0 D.R.m), finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) →
    ∃ c : ℂ, W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1) (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) =
        c • S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ∧
      ∀ Tm : (WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ),
        IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
          (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (S.N.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (S.N.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True) 1 (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) Tm →
        ∀ Φ : WO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) → ℂ,
          IsSBHalf e (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (G.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True) Φ →
          GlobalTheory.FirstRowVertex.rowShift0 S k (Tm Φ) =
            c • Tm (fun y => Φ (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
              (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
              (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) := by
  intro D T L sc G W U S μ₀ hL t e ht he k hk
  have hlat := GlobalTheory.FirstRowLat.rowPt0_inv_mem_stdLat_iff S hL ht k hk
  obtain ⟨c, hc⟩ := vac_first S k hlat
  refine ⟨c, hc, fun Tm hT Φ hΦ => ?_⟩
  exact GlobalTheory.LastVertexTensor.om_model S (GlobalTheory.LastVertexInv.defPair_chi (T := T) (firstIx D))
    (GlobalTheory.LastVertexInv.inRange_chi (T := T) (firstIx D)) he Tm hT _ c hlat hc Φ (sb_std_row S ht he (firstIx D) Φ hΦ)
