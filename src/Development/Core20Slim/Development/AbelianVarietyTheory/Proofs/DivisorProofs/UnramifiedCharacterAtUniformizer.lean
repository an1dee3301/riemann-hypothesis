module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.ChrWUnif

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

theorem valued_unifAt (v : Pl F) : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have hu : valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    e.lt_one_iff_lt_one.1 (hu ▸ uniformizer_lt_one)
  have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
  have hle1 : valuation (Fv F v) ((π : F) : Fv F v) ≤ valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) := by
    rw [hu, le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) := hπv ▸ (e _ _).1 hle1
  rw [← WithZero.exp_log h0] at hlt hge ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hge
  congr 1
  omega


end GlobalTheory.ChrWUnif
