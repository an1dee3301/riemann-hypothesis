module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatricesInvariantSupportedEqSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrices_invariant_supported_eq_smul : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {m k : ℕ}
    (S : AddSubgroup (Matrix (Fin m) (Fin k) (Fv F v))) (B : Set (Matrix (Fin m) (Fin k) (Fv F v)))
    (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : Matrix (Fin m) (Fin k) (Fv F v) → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB _) (hf0 : f ≠ 0)
    (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin k) (Fv F v)), (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) →
      ∃ c : ℂ, g = c • f),
    ∃ c : ℂ, f = c • (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))).indicator 1 ∧
      IsOpen (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) ∧ IsCompact (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) := by
  first | exact @GlobalTheory.SBClosure.main | exact GlobalTheory.SBClosure.main | (intros; apply GlobalTheory.SBClosure.main <;> assumption)
