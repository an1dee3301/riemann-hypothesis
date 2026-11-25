module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Core
public import Init.Data.Nat.Dvd
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem mfact_le_factorial_pow : ∀ (n : ℕ) (ν : Fin n → ℕ) (R : ℕ), (∀ i, ν i ≤ R) → ∀ mo : Fin n × Fin n →₀ ℕ, (∀ t, ∑ a, mo (a, t) = ν t) → mfact mo ≤ (R.factorial) ^ n := by
  intro n ν R hR mo hmo
  have h : mfact mo = ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial := by
    change (mo.prod fun _ k => k.factorial) = _
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type_right]
  rw [h]
  calc ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial ≤ ∏ _t : Fin n, R.factorial := by
        refine Finset.prod_le_prod' fun t _ => ?_
        refine le_trans (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ fun a => mo (a, t))) ?_
        rw [hmo t]
        exact Nat.factorial_le (hR t)
    _ = R.factorial ^ n := by simp

end GlobalTheory.TestLat
