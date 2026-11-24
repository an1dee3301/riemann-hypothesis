module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Batteries.Classes.Order
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Init.Core
public import Init.Data.Fin.Package
public import Init.Data.List.Basic
public import Init.Data.List.Count
public import Init.Data.Nat.Basic
public import Init.Data.Ord.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Order.Ord
public import Init.Data.Order.PackageFactories
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem mono_eq_prod_pow {n : ℕ} (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) (k : KG ε) :
    mono ε s k = ∏ c : Fin n × Fin n × Bool, coord ε c k ^ s.count c := by
  classical
  unfold mono
  rw [Finset.prod_list_map_count]
  have h := Finset.prod_subset (M := ℂ) (f := fun c => coord ε c k ^ s.count c) (Finset.subset_univ (s.toFinset))
    (fun c _ hc => by rw [List.count_eq_zero_of_not_mem (by simpa using hc), pow_zero])
  convert h using 4
  all_goals exact lawful_beq_subsingleton _ _

theorem finrank_polyV_le {n : ℕ} (ε : Fin n → Bool) (d : ℕ) :
    Module.finrank ℂ (polyV ε d) ≤ (d + 1) ^ (2 * n ^ 2) := by
  classical
  let b : ((Fin n × Fin n × Bool) → Fin (d + 1)) → (KG ε → ℂ) :=
    fun f k => ∏ c : Fin n × Fin n × Bool, coord ε c k ^ (f c : ℕ)
  have hle : polyV ε d ≤ Submodule.span ℂ (Set.range b) := by
    rw [polyV_eq]
    refine Submodule.span_le.2 ?_
    rintro φ ⟨s, hs, rfl⟩
    refine Submodule.subset_span ⟨fun c => ⟨s.count c, Nat.lt_succ_of_le ((List.count_le_length).trans hs)⟩, ?_⟩
    funext k
    rw [mono_eq_prod_pow]
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  calc Module.finrank ℂ (polyV ε d) ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range b)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card ((Fin n × Fin n × Bool) → Fin (d + 1)) := finrank_range_le_card b
    _ = (d + 1) ^ (2 * n ^ 2) := by
        simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        ring

end GlobalTheory.KFourier
