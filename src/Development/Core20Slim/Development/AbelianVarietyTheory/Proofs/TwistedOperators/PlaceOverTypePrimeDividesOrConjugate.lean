module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem div_or_isConjPl_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ IsConjPl PP' PP := by
  intro D P k PP h
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D P k PP h with h1 | ⟨w, h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨w, h1, fun c hc => ⟨Formalism.L2.Col.cO D.host.E c, ?_, rfl⟩⟩
    rw [h2, Formalism.L2.Col.conjIdeal_eq] at hc
    exact hc

end GlobalTheory.StepLaw
