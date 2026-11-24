module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.GroupWithZero.Prod
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem mixedTracePairing_nondegenerate_left {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, trP F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same] at this

theorem mixedTracePairing_nondegenerate_right {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F) (hy : ∀ x, trP F κ x y = 0) : y = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hy (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this

theorem mixedTracePairing_nondegenerate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (trP F κ).Nondegenerate := by
  intro F _ _ κ _
  refine ⟨fun x hx => mixedTracePairing_nondegenerate_left (F := F) (κ := κ) x hx, fun y hy => mixedTracePairing_nondegenerate_right (F := F) (κ := κ) y hy⟩

end GlobalTheory.ArchSch
