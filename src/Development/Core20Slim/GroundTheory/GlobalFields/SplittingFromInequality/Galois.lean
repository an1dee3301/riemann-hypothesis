module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.SplittingFromInequality
public import Development.Core20Slim.GroundTheory.GlobalFields.KummerTheory.Splitting
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Unique
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter Module AdeleBaseChange

noncomputable section

section Tower

variable {K K' L : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]


omit [NumberField K] [NumberField L] in
theorem SplitsCompletely.of_liesOver {v : HeightOneSpectrum (𝓞 K)} (hv : SplitsCompletely L v)
    (v' : HeightOneSpectrum (𝓞 K')) [v'.asIdeal.LiesOver v.asIdeal] : SplitsCompletely L v' := by
  intro w hw
  have : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal v'.asIdeal v.asIdeal
  obtain ⟨he, hf⟩ := hv w this
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) v'.asIdeal w.asIdeal] at he
  rw [Ideal.inertiaDeg_tower (R := 𝓞 K) v'.asIdeal w.asIdeal] at hf
  exact ⟨(mul_eq_one.1 he).2, (mul_eq_one.1 hf).2⟩



end Tower

section Galois

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



end Galois

end

end GroundTheory.Global
