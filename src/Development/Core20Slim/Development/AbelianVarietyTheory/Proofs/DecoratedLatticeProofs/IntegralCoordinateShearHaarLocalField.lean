module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Range
public import Mathlib.Algebra.Order.Monoid.Units
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.CoordShear

theorem measurePreserving_shear {k : Type} [AddCommGroup k] [MeasurableSpace k] [MeasurableAdd₂ k]
    (ν : Measure k) [SigmaFinite ν] [ν.IsAddLeftInvariant]
    {J : Type} [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k))
    (hg : Measurable g) (h1 : ∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y')
    (h2 : ∀ (y : J → k) j, j ∉ S → g y j = 0) :
    MeasurePreserving (fun y => y + g y) (Measure.pi fun _ : J => ν) (Measure.pi fun _ : J => ν) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => k) (fun j => j ∉ S) with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : J => ν)
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : J => ν) (fun j => j ∉ S)
  let G : ({j // j ∉ S} → k) → ({j // ¬ j ∉ S} → k) := fun b i => g (e.symm (b, 0)) i
  have hG : Measurable G := by
    refine Measurable.of_eval fun i => ?_
    exact (measurable_pi_apply (i : J)).comp
      (hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hΦ : MeasurePreserving
      (fun p : ({j // j ∉ S} → k) × ({j // ¬ j ∉ S} → k) => (id p.1, G p.1 + p.2))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) := by
    refine (MeasurePreserving.id _).skew_product (g := fun b a => G b + a) ?_ ?_
    · exact (hG.comp measurable_fst).add measurable_snd
    · exact Filter.Eventually.of_forall fun b => (measurePreserving_add_left _ (G b)).map_eq

  have hGy : ∀ y : J → k, g (e.symm ((e y).1, 0)) = g y := by
    intro y
    refine h1 _ _ fun j hj => ?_
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have key : (fun y => y + g y) = e.symm ∘ (fun p => (id p.1, G p.1 + p.2)) ∘ e := by
    funext y
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h2 y i i.2]
    · have := congrFun (hGy y) i
      simp only [G, Pi.add_apply]
      rw [this]
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, add_comm]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΦ.comp he_mp)

theorem integral_shear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k)), Continuous g → (∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y') → (∀ (y : J → k) j, j ∉ S → g y j = 0) → ∀ F : (J → k) → ℂ, ∫ y, F (y + g y) ∂(Measure.pi fun _ => ν) = ∫ y, F y ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ν hν J _ _ S g hg h1 h2 F

  have : SecondCountableTopology k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    let : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    let : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    exact secondCountable_of_proper
  have := hν
  have hgm : Measurable g := hg.measurable
  have hmp := measurePreserving_shear ν S g hgm h1 h2
  have hfix : ∀ y, g (y + g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hfix' : ∀ y, g (y - g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hsurj : Function.Surjective (fun y : J → k => y + g y) :=
    fun y => ⟨y - g y, by simp [hfix']⟩
  have hemb : MeasurableEmbedding (fun y : J → k => y + g y) :=
    MeasurableEmbedding.of_measurable_inverse (g := fun y => y - g y) (measurable_id.add hgm)
      (by rw [hsurj.range_eq]; exact MeasurableSet.univ) (measurable_id.sub hgm)
      (fun y => by simp [hfix])
  exact hmp.integral_comp hemb F

end GlobalTheory.CoordShear
