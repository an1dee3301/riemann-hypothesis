module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Abel

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacCoefAtPlace

open GlobalTheory.ArchRec GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

theorem foldr_lin {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (hA : ∀ i f, P f → P (A i f))
    (hl : ∀ i (a : ℂ) f f', P f → P f' → A i (a • f + f') = a • A i f + A i f')
    (a : ℂ) {f f' : X → ℂ} (hf : P f) (hf' : P f') (l : List ι) :
    l.foldr (fun i g => A i g) (a • f + f') =
      a • l.foldr (fun i g => A i g) f + l.foldr (fun i g => A i g) f' := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact hl i a _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l) (GlobalTheory.FockIndep.foldr_mem hA hf' l)

theorem pure_lin {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (hA : ∀ i f, P f → P (A i f))
    (hl : ∀ i (a : ℂ) f f', P f → P f' → A i (a • f + f') = a • A i f + A i f')
    (a : ℂ) {f f' : X → ℂ} (hf : P f) (hf' : P f') (Q : MvPolynomial ι ℂ) :
    pureTensorL A (a • f + f') Q = a • pureTensorL A f Q + pureTensorL A f' Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [foldr_lin hA hl a hf hf', smul_add, smul_comm c a]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, smul_add]
    abel





end GlobalTheory.VacCoefAtPlace

namespace GlobalTheory.VacCoefAtPlace

open GlobalTheory.ArchRec GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}





end GlobalTheory.VacCoefAtPlace

namespace GlobalTheory.VacCoefAtPlace

open GlobalTheory.ArchRec GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting


end GlobalTheory.VacCoefAtPlace
