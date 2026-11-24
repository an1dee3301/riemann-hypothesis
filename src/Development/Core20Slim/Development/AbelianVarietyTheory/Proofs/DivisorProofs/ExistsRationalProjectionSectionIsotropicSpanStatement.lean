module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalProjectionSectionIsotropicSpan
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_projection_section_isotropicSpan : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  first | exact @GlobalTheory.rational_proj_section_of_span | exact GlobalTheory.rational_proj_section_of_span | (intros; apply GlobalTheory.rational_proj_section_of_span <;> assumption)
