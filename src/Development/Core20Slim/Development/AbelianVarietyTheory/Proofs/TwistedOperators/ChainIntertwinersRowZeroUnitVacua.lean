module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
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
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.RowArrows

theorem vY_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) {k : ℕ} (hk : k + 1 < D.R.m) : R.vY t k ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D k) (Yc D (k + 1)) // a.map (infPart D) = 0} => heisO R.ψ _ _ a (R.vac k)) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ hk)) (h.chain.vY t k hk)

theorem vX_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) : R.vX t ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D (D.R.m - 1)) D.sp.X' // a.map (infPart D) = 0} => heisO R.ψ _ _ a R.vacX) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by have := D.R.two_le_m; omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h.lev.βX) (h.chain.vX t)

theorem chainIntertwiners_rowZero_unitVacua : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → IsItW R.θ (GlobalTheory.Grid.row0 R j).M (GlobalTheory.Grid.row0 R (j + 1)).M (GlobalTheory.Grid.th0 R t j).ω (GlobalTheory.Grid.fock R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac) (GlobalTheory.Grid.th0 R t j).It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F h _ G' W _ G _ _ _ _ t j hj
  unfold GlobalTheory.Grid.th0
  by_cases h1 : j + 1 < D.R.m
  · rw [dite_eq_left h1]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepY R t j)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R h1))
    have hω := h.chain.ωY t j h1
    rw [GlobalTheory.Grid.chrStep_eq_muAt] at hω
    exact (hc.2 ⟨hω, (h.chain.vY t j h1).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vY t j h1).1.2.theta (vY_mem_span_core h t h1) (h.chain.ItY t j h1)⟩).intw
  · have h2 : j + 1 = D.R.m := by omega
    rw [dite_eq_right h1, dite_eq_left h2]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepX R t)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_pred_eq_chainVertexAtRowZero_last R h2) (GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R h1))
    have hω := h.chain.ωX t
    rw [(congrArg _ h2.symm).trans (GlobalTheory.Grid.chrStep_eq_muAt R t j)] at hω
    exact (hc.2 ⟨hω, (h.chain.vX t).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vX t).1.2.theta (vX_mem_span_core h t) (h.chain.ItX t)⟩).intw

end GlobalTheory.GridJoin.RowArrows

end
