module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Tactic.Push

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.GoodPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]








end General

theorem isSplitPl_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (P : HeightOneSpectrum (𝓞 H.E)) :
    IsSplitPl H P ↔ ∃ P', P ≠ P' ∧ P'.under (𝓞 H.F) = P.under (𝓞 H.F) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨P', hP', -⟩ := existsUnique_conjPl c.toRingEquiv P
    refine ⟨P', ?_, (under_eq_iff_conjPl c hcm.rank hcm.ne P P').2 (Or.inr hP')⟩
    rintro rfl
    exact hy (RingOfIntegers.mapRingEquiv c.toRingEquiv x) (hc x) (((conjPl_iff_mem _ P P).1 hP' x _ rfl).1 hx)
  · rintro ⟨P', hne, hu⟩
    have hP' := ((under_eq_iff_conjPl c hcm.rank hcm.ne P P').1 hu).resolve_left hne.symm
    rw [conjPl_iff_mem] at hP'
    by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    refine hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun y hy => ?_).symm)
    have hxy : (y : H.E) = c.toRingEquiv ((RingOfIntegers.mapRingEquiv c.toRingEquiv).symm y : 𝓞 H.E) :=
      congrArg (fun z : 𝓞 H.E => (z : H.E)) ((RingOfIntegers.mapRingEquiv c.toRingEquiv).apply_symm_apply y).symm
    obtain ⟨z, hz, hzP⟩ := hn _ ((hP' _ y hxy).2 hy)
    have e : z = y := RingOfIntegers.ext (hz.trans ((hc _).symm.trans hxy.symm))
    exact e ▸ hzP



end GlobalTheory.Mem.GoodPlace
