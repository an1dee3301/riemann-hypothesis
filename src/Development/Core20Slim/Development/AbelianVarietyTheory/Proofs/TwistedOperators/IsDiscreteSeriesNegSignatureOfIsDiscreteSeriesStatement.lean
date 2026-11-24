module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesNegSignatureOfIsDiscreteSeries
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteSeries_neg_signature_of_isDiscreteSeries : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  first | exact @GlobalTheory.PairLift.isDS_flip | exact GlobalTheory.PairLift.isDS_flip | (intros; apply GlobalTheory.PairLift.isDS_flip <;> assumption)
