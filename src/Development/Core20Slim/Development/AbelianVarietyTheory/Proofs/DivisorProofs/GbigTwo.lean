module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

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

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Chars)

theorem gbig_two {Q1 Q2 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_max_right _ _) hC) D large₂ hε (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def Carried (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) {A A' WW : HSp D} (X : Tri T A A' WW)
    (Bs : Base D.host.F D.host.E) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Γ : Geo D.sp.cm.sig A.rank A'.rank) (s : T) : Prop :=
  GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f s) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' s) ∧
    (∀ P g h, thetaKO (X.ω s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f s) P) = X.ker W.ψ W.θ s P h g) ∧
    (∀ P g h, thetaKO (X.ω' s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' s) P) = X.ker' W.ψ W.θ s P h g) ∧
    ∀ om om', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' →
      ∃ e cA cB, GlobalTheory.SquareAgree.IsOver W.ψ W.θ FA FA' FW (GlobalTheory.SqStep.chs G i j s).α (GlobalTheory.SqStep.chs G i j s).β X.m X.fd
        X.m' X.fd' (X.ω s) (X.ω' s) e Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' cA cB

end GlobalTheory.SqStepBig

end
