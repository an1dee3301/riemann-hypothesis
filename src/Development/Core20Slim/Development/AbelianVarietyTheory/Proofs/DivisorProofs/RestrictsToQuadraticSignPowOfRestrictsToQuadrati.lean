module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LFun

open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
private theorem isUnit_of_isUnit_norm' {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (z : S) (h : IsUnit (Algebra.norm R z)) : IsUnit z := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det] at h
  obtain ⟨u, hu⟩ := h
  refine IsUnit.of_mul_eq_one (u.inv 1) ?_
  have := congrArg (fun f : Module.End R S => f 1) u.val_inv
  simp only [hu] at this
  simpa using this


open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
theorem _root_.GlobalTheory.LFun.resEtaPow_of_resEta : ∀ (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (χ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)ˣ →* Circle) (n : ℕ), _root_.GlobalTheory.LFun.ResEta F E χ n →
      _root_.GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).toMonoidHom).range χ n := by
  intro F E _ _ _ _ _ h2 χ n hχ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨⟨η, hη⟩, hall⟩ := hχ
  have hηe := hη.eq_normSign
  intro a
  rw [show χ ((Units.map ↑(algebraMap (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E))) a) = η a ^ n from
    hall η hη a]
  split_ifs with ha
  · obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 ha
    obtain ⟨t, rfl⟩ := hy
    obtain ⟨w, rfl⟩ := hz
    rw [map_mul, hη.2.1 t, hη.2.2.1 w]
    simp
  · have hs : _root_.GlobalTheory.IdeleNormChar.normSign E a ≠ 1 := by
      intro h1
      obtain ⟨t, ht⟩ := (_root_.GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 h1
      obtain ⟨z, hz⟩ := _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff.1 ht
      have hzu : IsUnit z :=
        isUnit_of_isUnit_norm' z (hz ▸ Units.isUnit _)
      apply ha
      have hn : Units.map (Algebra.norm (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hzu.unit =
          a / _root_.GlobalTheory.QuadSymbol.toUnits F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) t := by
        ext
        simpa using hz
      have key : a = _root_.GlobalTheory.QuadSymbol.toUnits F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) t *
          Units.map (Algebra.norm (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hzu.unit := by
        rw [hn, mul_div_cancel]
      rw [key]
      exact mul_mem (Subgroup.mem_sup_left ⟨t, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)
    have hm : _root_.GlobalTheory.IdeleNormChar.normSign E a = -1 := (Int.units_eq_one_or _).resolve_left hs
    rw [hηe]
    simp [hm, _root_.GlobalTheory.IdeleNormChar.signToCircle]

end GlobalTheory.LFun
