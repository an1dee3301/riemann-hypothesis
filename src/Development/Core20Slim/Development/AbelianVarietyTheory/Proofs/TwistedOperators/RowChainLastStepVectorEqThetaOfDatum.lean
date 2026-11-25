module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
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
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTopChain


open Classical in
theorem transport {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (k : ℕ)
    (P : Finset (Pl D.host.E)) (ψ : AddChar (AF D.host.F) ℂ) (e : AE D)
    {S S' : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {X Y : LSp D} (hX : X = ⟨S, ΛS⟩) (hY : Y = ⟨S', ΛS'⟩)
    {βS : GL (Fin X.sp.rank) (EAf D)} {βT : GL (Fin Y.sp.rank) (EAf D)} {βS₀ : GL (Fin S.rank) (EAf D)}
    {βT₀ : GL (Fin S'.rank) (EAf D)} (h1 : HEq βS βS₀) (h2 : HEq βT βT₀)
    {f₀ g : WO X.sp Y.sp → ℂ} {f₀' g' : WO S S' → ℂ} (h3 : HEq f₀ f₀') (h4 : HEq g g')
    (ha : X.sp.rank = D.R.r + k * D.R.t) (hb : Y.sp.rank = D.R.r + (k + 1) * D.R.t)
    (ha' : S.rank = D.R.r + k * D.R.t) (hb' : S'.rank = D.R.r + (k + 1) * D.R.t)
    (Ω : Matrix (Fin S'.rank) (Fin S.rank) (EAf D) → ℂ)
    (hN : ∀ N, IsIntM N → Ω N = ∏ w ∈ P, stepFn L t w k
      ((N.map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb') (Comparison₂.ixOf G t w ha')))
    (hθ : IsThetaAt ψ (symplO S S') (heisO ψ S S') e (latO S S' (ΛS : Set _) (ΛS' : Set _) fun _ => True) 1 f₀'
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S S' βS₀ βT₀ x) then Ω (frMapO S S' βS₀ βT₀ x) else 0) g') :
    IsThetaAt ψ (symplO X.sp Y.sp) (heisO ψ X.sp Y.sp) e (latO X.sp Y.sp (X.lat : Set _) (Y.lat : Set _) fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D))) then
        ∏ w ∈ P, stepFn L t w k (((Comparison₂.fr βT βS (x.map (toEAf D))).map (cpt (D := D) w)).submatrix
          (Comparison₂.ixOf G t w hb) (Comparison₂.ixOf G t w ha)) else 0) g := by
  subst hX hY
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h4
  convert hθ using 2
  rename_i x
  by_cases h : IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D)))
  · have h' : IsHalf e x ∧ IsIntM (frMapO S S' βS βT x) := h
    rw [if_pos h, if_pos h']
    exact (hN _ h.2).symm
  · have h' : ¬ (IsHalf e x ∧ IsIntM (frMapO S S' βS βT x)) := h
    rw [if_neg h, if_neg h']

end GlobalTheory.FlipTopChain

namespace GlobalTheory.FlipTopChain

theorem colY_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → columnBlock L n = ⟨D.sp.X', L.ΛX⟩ := by
  rintro _ rfl; exact colY_m L

theorem colFrame_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → HEq (colFrame L n) L.βX := by
  rintro _ rfl; exact colFrame_m L


set_option maxHeartbeats 1600000 in
theorem last_step_theta : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F large₂ hS ch hch t j g hj hg
  obtain ⟨k, hk⟩ := j
  simp only at hj
  obtain rfl : k = D.R.m - 1 := by omega
  obtain ⟨-, e', he', hθ⟩ := hS.core.chain.vX t
  refine ⟨e', he', ?_⟩
  have hm : D.R.m - 1 < D.R.m := hk
  have hb' : D.sp.X'.rank = D.R.r + (D.R.m - 1 + 1) * D.R.t := by
    rw [hj]; exact D.sp.X'_rank
  have hN := (Comparison₂.local_factors ch.S.B t hS.core.lev).2.2 (D.R.m - 1) hm _ hb'
  have hchi : R.toLevCh.chi (D.R.m - 1 + 1) = R.toLevCh.chi D.R.m := by rw [hj]
  rw [hchi] at hN
  unfold GlobalTheory.FlipTop.topFn
  exact transport ch.G t (D.R.m - 1) _ ch.W.ψ e' (X := ch.G.node (.grid 0 (D.R.m - 1)))
    (Y := ch.G.node (.grid 0 (D.R.m - 1 + 1))) (colY_lt R.toLevCh hm) (colY_eq_m R.toLevCh _ hj)
    (colFrame_lt R.toLevCh hm) (colFrame_eq_m R.toLevCh _ hj) (hch.vac.2 _ hj) hg _ _ (Comparison₂.rank_Yc hm.le) hb' _ hN
    (hch.weil.ψ ▸ hθ)

end GlobalTheory.FlipTopChain

end
