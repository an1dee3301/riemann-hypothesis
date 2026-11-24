module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellP
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.HermitianForms.AdelicCharacterLocalNontrivial
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

theorem exists_norm_lt_one' : ∃ ϖ : Fv F v, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  exact NormedField.exists_norm_lt_one _

variable {v}

theorem continuous_psiV' {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) : Continuous (psiV F ψ v) :=
  ((GlobalTheory.T.adelic_character_local_nontrivial F ψ hψ).1 v).1

theorem psiV_add' (ψ : AddChar (AF F) ℂ) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y := by
  have h : pairA F 0 (singleV F v (x + y)) = pairA F 0 (singleV F v x) + pairA F 0 (singleV F v y) := by
    simp only [pairA, singleV, RestrictedProduct.single_add]
    exact Prod.ext (add_zero _).symm rfl
  simp only [psiV]; rw [h, AddChar.map_add_eq_mul]

theorem psiV_zero' (ψ : AddChar (AF F) ℂ) : psiV F ψ v 0 = 1 := by
  have h : pairA F 0 (singleV F v 0) = 0 := by
    simp only [pairA, singleV, RestrictedProduct.single_zero]; rfl
  simp only [psiV]; rw [h, AddChar.map_zero_eq_one]

theorem norm_psiV' {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : Fv F v) : ‖psiV F ψ v x‖ = 1 :=
  hψ.2.1 _

theorem exists_psiV_ne_one' {σ : E →ₐ[F] E} (_hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ y, psiV F ψ v y ≠ 1 :=
  ((GlobalTheory.T.adelic_character_local_nontrivial F ψ hψ).1 v).2

end PositivityTheory.SiegelWeilFormula.SwLocFin
