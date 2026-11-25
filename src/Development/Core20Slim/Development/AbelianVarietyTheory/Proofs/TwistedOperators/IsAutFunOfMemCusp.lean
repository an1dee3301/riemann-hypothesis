module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem row_induction {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (C : ∀ i, Set (Fn G (.grid i 0))) : ∀ (n : ℕ) (f : ∀ i : Fin n, Sch G (.right (i : ℕ) 0)),
    (∀ (i : Fin n) F, F ∈ C i → LiftConv W M (.right (i : ℕ) 0) (f i) F ∧
      liftA W M (.right (i : ℕ) 0) (f i) F ∈ C ((i : ℕ) + 1)) →
    ∀ F ∈ C 0, PathConv W M (rowPath T 0 n) (rowFam 0 n f) F ∧ liftP W M (rowPath T 0 n) (rowFam 0 n f) F ∈ C n
  | 0, _, _, _, hF => ⟨trivial, hF⟩
  | n + 1, f, h, F, hF => by
    have ih := row_induction W M C n (fun i => f i.castSucc) (fun i F hF => h i.castSucc F hF) F hF
    have := h (Fin.last n) _ ih.2
    exact ⟨⟨ih.1, this.1⟩, this.2⟩

theorem isAutFun_zero (V : HSp D) : IsAutFun V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩

theorem isAutFun_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsAutFun V f) (hg : IsAutFun V g) : IsAutFun V (f + g) := by
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨U', hU', h'⟩ := hg.level
  refine ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x], ⟨U ⊓ U', hU.inter hU', fun k hk hf x => ?_⟩,
    hf.cont.add hg.cont⟩
  simp only [Pi.add_apply, h k hk.1 hf x, h' k hk.2 hf x]

theorem isAutFun_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsAutFun V f) (a : ℂ) : IsAutFun V (a • f) := by
  obtain ⟨U, hU, h⟩ := hf.level
  refine ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.left γ hγ x], ⟨U, hU, fun k hk hf x => ?_⟩, hf.cont.const_smul a⟩
  simp only [Pi.smul_apply, h k hk hf x]

theorem isAutFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, IsAutFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => (hx.aut w).toIsAutFun
    | zero => exact fun w => isAutFun_zero _
    | add x y _ _ hx hy => exact fun w => isAutFun_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => isAutFun_smul (hx w) c
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using isAutFun_smul (hU' f) r
  | add x y hx hy => simpa using isAutFun_add hx hy

theorem start_mem {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (u : R.HE.H) :
    PiTensorProduct.lift (R.HE.e u) ∈ (GlobalTheory.Grid.nodeY R 0).Cusp R.θ := by
  have h1 : R.HE.e u ∈ R.EEat R.triv := h.models.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have h2 := Formalism.IndefR.Mult.goodPart_le R.θ (R.MY 0) _ _ _ h1
  exact GlobalTheory.Grid.Node.multT_le_cusp (GlobalTheory.Grid.nodeY R 0) R.θ _ _ (Submodule.mem_map_of_mem h2)

theorem rowBase_of_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
  ⟨h.lev, h.models.inf, h.models.νY, h.models.νY', h.models.νX⟩

end GlobalTheory.RowLift

end
