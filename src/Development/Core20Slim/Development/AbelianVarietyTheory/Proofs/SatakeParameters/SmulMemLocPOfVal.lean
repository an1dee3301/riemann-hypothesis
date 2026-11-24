module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

noncomputable section

namespace GlobalTheory.JetOpWeylLat

open GlobalTheory.JetPoint  Formalism.GradedWeylDivisibility

section Expand

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}





end Expand

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem toK_map_int {σ : Type} (f : MvPolynomial σ ℤ) :
    toK K σ (map (Int.castRingHom (𝓞 K)) f) = map (Int.castRingHom K) f := by
  change map (algebraMap (𝓞 K) K) _ = _
  rw [map_map]
  congr 1




theorem smul_mem_localizationAt_of_valuation (w : HeightOneSpectrum (𝓞 K)) {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    [IsScalarTower (𝓞 K) K Z] {T : Submodule (𝓞 K) Z} {x : K}
    (hx : w.valuation K x ≤ 1) {P : Z} (hP : P ∈ T) : x • P ∈ localization₂ w.asIdeal T := by
  obtain ⟨r, ⟨d, hd⟩, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have h' : algebraMap (𝓞 K) K d * x = algebraMap (𝓞 K) K r := (mul_comm _ _).trans h
  have e : d • x • P = r • P := by
    rw [← algebraMap_smul K d (x • P), smul_smul, h', algebraMap_smul]
  exact ⟨d, hd, e ▸ T.smul_mem r hP⟩



end GlobalTheory.JetOpWeylLat
