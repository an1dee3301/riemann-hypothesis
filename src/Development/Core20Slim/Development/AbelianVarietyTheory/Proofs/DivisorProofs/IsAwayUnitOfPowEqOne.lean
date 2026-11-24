module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ChiGrid
open GlobalTheory.SqTop (twPl Qn)
open GlobalTheory.Square (IsAwayUnit)
open GlobalTheory.RowTest (LocIn NumbersIn)

namespace GlobalTheory.KappaArith

theorem isAwayUnit_of_pow_eq_one {K : Type} [Field K] (m : ℕ) {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsAwayUnit m z := by
  have hint : IsIntegral ℤ z :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hz]⟩
  let a : 𝓞 K := ⟨z, hint⟩
  have ha : (a : K) = z := rfl
  refine ⟨a, 0, 0, ⟨a ^ (n - 1), ?_⟩, by simp [ha]⟩
  rw [pow_zero]
  apply RingOfIntegers.ext
  have e1 : ((a * a ^ (n - 1) : 𝓞 K) : K) = z * z ^ (n - 1) := by rw [← ha]; norm_cast
  rw [e1, ← pow_succ', Nat.sub_add_cancel hn, hz]
  rfl

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)

def AwayIm (D : D7) (m : ℕ) (z : ℂ) : Prop := ∃ ζ : D.what₂.LL, IsAwayUnit m ζ ∧ D.what₂.embLL ζ = z

theorem awayIm_one (m : ℕ) : AwayIm D m 1 := ⟨1, IsAwayUnit.one m, map_one _⟩

theorem AwayIm.mul {m : ℕ} {z z' : ℂ} (h : AwayIm D m z) (h' : AwayIm D m z') : AwayIm D m (z * z') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

theorem AwayIm.prod {m : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, AwayIm D m (f i)) :
    AwayIm D m (∏ i ∈ s, f i) :=
  Finset.prod_induction f (AwayIm D m) (fun _ _ => AwayIm.mul) (awayIm_one m) h

theorem awayIm_val {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (x : (w.adicCompletion D.host.E)ˣ) :
    AwayIm D m ((Lc.xiH t).loc w x : ℂ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨ζ, hζ⟩ := hx w x
  have h1 : ((Lc.xiH t).loc w x) ^ n = 1 := by
    have : ((Lc.xiH t) ^ n).loc w x = 1 := by rw [show (Lc.xiH t) ^ n = 1 from ho]; rfl
    exact this
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.KappaArith

end
