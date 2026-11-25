module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissibleForm_adelicThetaSum : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ], ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  first | exact @GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | exact GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | (intros; apply GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact <;> assumption)
