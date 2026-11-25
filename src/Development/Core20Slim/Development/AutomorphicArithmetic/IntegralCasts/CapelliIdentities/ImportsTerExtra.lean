module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineIndex
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

theorem UpperTheory.Reformulated.B.Gub1.proof.{u_1, u_2} :
    ∀ (E : Type u_1) (W : Type u_2) [inst : Field E] [inst_1 : NumberField E] [inst_2 : AddCommGroup W]
      [inst_3 : _root_.Module E W], GroundTheory.Heights₂.Heights.FiniteCovolume.LineIndexNeZero.Statement E W := by
  intro E W _ _ _ _ La x hL _ _
  have hfg : (La ⊓ (Submodule.span E {x}).toAddSubgroup).FG :=
    (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule _)).1
      (((Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule La)).2 hL.fg).of_le
        (AddSubgroup.toIntSubmodule.monotone inf_le_left))
  have := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine @AddSubgroup.index_ne_zero_of_finite _ _ _ (AddCommGroup.finite_of_fg_isAddTorsion _ ?_)
  rintro ⟨y, hy', hy⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨n, hn, hc⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
    (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨n, hn, (QuotientAddGroup.eq_zero_iff (n • _)).2 ?_⟩
  exact ⟨⟨n • c, hc⟩, smul_assoc n c x⟩
