module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.SUnitsExact
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.SUnitsRep
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.LatticeBridge
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

namespace GroundTheory.Global

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct

noncomputable section

section Log

open scoped Classical

variable (L : Type*) [Field L] [NumberField L]

def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun x w := (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L)))
  map_zero' := by
    funext w
    simp
  map_add' x y := by
    funext w
    simp only [toMul_add, Units.val_mul, map_mul, Pi.add_apply]
    rw [Real.log_mul (pos_at_place _ w).ne' (pos_at_place _ w).ne', mul_add]

omit [NumberField L] in
theorem fullLog_apply (x : Additive (𝓞 L)ˣ) (w : InfinitePlace L) :
    fullLog L x w = (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L))) :=
  rfl

theorem sum_fullLog (x : Additive (𝓞 L)ˣ) : ∑ w, fullLog L x w = 0 :=
  sum_mult_mul_log x.toMul

def logLattice : Submodule ℤ (InfinitePlace L → ℝ) :=
  LinearMap.range (fullLog L).toIntLinearMap

def logProj : (InfinitePlace L → ℝ) →ₗ[ℝ] logSpace L :=
  LinearMap.funLeft ℝ ℝ Subtype.val

theorem logProj_fullLog (x : Additive (𝓞 L)ˣ) : logProj L (fullLog L x) = logEmbedding L x :=
  rfl

theorem fullLog_eq_zero_iff (x : Additive (𝓞 L)ˣ) : fullLog L x = 0 ↔ x.toMul ∈ torsion L := by
  constructor
  · intro h
    rw [← logEmbedding_eq_zero_iff, ofMul_toMul, ← logProj_fullLog, h, map_zero]
  · intro h
    rw [mem_torsion] at h
    funext w
    rw [fullLog_apply, h w, Real.log_one, mul_zero, Pi.zero_apply]

theorem logProj_mem_unitLattice (m : logLattice L) : logProj L m ∈ unitLattice L := by
  obtain ⟨x, hx⟩ := m.2
  rw [← hx]
  exact ⟨x, trivial, rfl⟩

def logLatticeEquiv : logLattice L ≃ₗ[ℤ] unitLattice L :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (unitLattice L) ((logProj L).restrictScalars ℤ ∘ₗ (logLattice L).subtype)
      (logProj_mem_unitLattice L)) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro m hm
      obtain ⟨x, hx⟩ := m.2
      have h1 : logEmbedding L x = 0 := by
        rw [← logProj_fullLog]
        have := congrArg Subtype.val hm
        simp only [ZeroMemClass.coe_zero] at this
        change logProj L (fullLog L x) = 0
        rw [show fullLog L x = (m : InfinitePlace L → ℝ) from hx]
        exact this
      rw [← ofMul_toMul x, logEmbedding_eq_zero_iff, ← fullLog_eq_zero_iff] at h1
      apply Subtype.ext
      rw [← hx]
      exact h1
    · rintro ⟨y, x, -, rfl⟩
      exact ⟨⟨fullLog L x, x, rfl⟩, rfl⟩

instance : Module.Free ℤ (logLattice L) :=
  have := ZLattice.module_free ℝ (unitLattice L)
  Module.Free.of_equiv (logLatticeEquiv L).symm

instance : Module.Finite ℤ (logLattice L) :=
  have := ZLattice.module_finite ℝ (unitLattice L)
  Module.Finite.equiv (logLatticeEquiv L).symm

theorem finrank_logLattice : finrank ℤ (logLattice L) = rank L :=
  (logLatticeEquiv L).finrank_eq.trans (unitLattice_rank L)

theorem linearIndependent_logLattice_basis {ι : Type*} (b : Basis ι ℤ (logLattice L)) :
    LinearIndependent ℝ (fun i => (b i : InfinitePlace L → ℝ)) := by
  apply LinearIndependent.of_comp (logProj L)
  have := ((b.map (logLatticeEquiv L)).ofZLatticeBasis ℝ (unitLattice L)).linearIndependent
  convert this using 1
  · funext i
    rw [Basis.ofZLatticeBasis_apply, Basis.map_apply]
    rfl

end Log

section Galois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem mult_smul (g : L ≃ₐ[K] L) (w : InfinitePlace L) : (g • w).mult = w.mult := by
  have := isReal_smul_iff (σ := g) (w := w)
  unfold mult
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl

omit [NumberField K] [NumberField L] in
theorem fullLog_unitsRep (g : L ≃ₐ[K] L) (x : Additive (𝓞 L)ˣ) :
    fullLog L (unitsRep K L g x) = funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (fullLog L x) := by
  funext w
  rw [funPermRep_apply, fullLog_apply, fullLog_apply, mult_smul, unitsRep_apply, toMul_ofMul,
    InfinitePlace.smul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  rfl

omit [NumberField K] [NumberField L] in
theorem funPermRep_mem_logLattice (g : L ≃ₐ[K] L) {m : InfinitePlace L → ℝ}
    (hm : m ∈ logLattice L) : funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m ∈ logLattice L := by
  obtain ⟨x, rfl⟩ := hm
  exact ⟨unitsRep K L g x, fullLog_unitsRep g x⟩

variable (K L) in
def logLatticeRep : Representation ℤ (L ≃ₐ[K] L) (logLattice L) where
  toFun g := ((funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g).restrictScalars ℤ).restrict
    fun _ hm => funPermRep_mem_logLattice g hm
  map_one' := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((1 : L ≃ₐ[K] L)⁻¹ • w) = (m : InfinitePlace L → ℝ) w
    rw [inv_one, one_smul]
  map_mul' g h := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((g * h)⁻¹ • w) = (m : InfinitePlace L → ℝ) (h⁻¹ • g⁻¹ • w)
    rw [mul_inv_rev, mul_smul]

omit [NumberField K] [NumberField L] in
theorem coe_logLatticeRep (g : L ≃ₐ[K] L) (m : logLattice L) :
    (logLatticeRep (K := K) (L := L) g m : InfinitePlace L → ℝ) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m :=
  rfl

variable [FiniteDimensional K L]

omit [NumberField K] in
theorem cycHerbrand_unitsRep_eq_logLattice {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (unitsRep K L) σ = cycHerbrand (logLatticeRep (K := K) (L := L)) σ := by
  let p : Additive (𝓞 L)ˣ →+ logLattice L := (fullLog L).toIntLinearMap.rangeRestrict.toAddMonoidHom
  have hp : Function.Surjective p := (fullLog L).toIntLinearMap.surjective_rangeRestrict
  have : Finite p.ker := by
    refine Finite.of_injective (β := torsion L)
      (fun x => ⟨(x : Additive (𝓞 L)ˣ).toMul, (fullLog_eq_zero_iff L x).1 ?_⟩) ?_
    · have := congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)
      exact this
    · intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Additive.toMul.injective h)
  exact cycHerbrand_eq_of_surjective_of_finite_ker (unitsRep K L)
    (logLatticeRep (K := K) (L := L)) σ hp
    (fun g x => Subtype.ext (fullLog_unitsRep g x))
    (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)

end Galois

end

end GroundTheory.Global
