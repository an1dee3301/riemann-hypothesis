module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_of_bilinear_schwartzBruhatProduct : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  first | exact @GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | exact GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | (intros; apply GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB <;> assumption)
