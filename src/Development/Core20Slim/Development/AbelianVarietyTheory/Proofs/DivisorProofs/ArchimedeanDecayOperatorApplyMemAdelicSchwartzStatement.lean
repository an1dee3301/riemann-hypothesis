module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ), ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  first | exact @GlobalTheory.ArchDecay.SchAStab.app_mem_schA | exact GlobalTheory.ArchDecay.SchAStab.app_mem_schA | (intros; apply GlobalTheory.ArchDecay.SchAStab.app_mem_schA <;> assumption)
