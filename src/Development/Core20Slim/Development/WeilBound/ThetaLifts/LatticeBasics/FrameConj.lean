module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Frame

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open Formalism.UG (bc)

section Generic

variable {S R β : Type} [CommRing S] [CommRing R] [Fintype β] [DecidableEq β]








end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}


variable (F) in
def eF : AF F := LinearMap.inr F (Ainf F) (Af F) 1

omit [NumberField E] in
theorem smul_incl (a : AF F) (x : E) : a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := by
  change (a * 1) ⊗ₜ[F] x = _
  rw [mul_one]

theorem mem_latHat (hL : Y.L.FG) (z : Fin n → AE F E) :
    z ∈ latHat Y ↔ eF F • z = z ∧ ∀ v, compFin F E v ∘ z ∈ latLoc F Y.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      refine ⟨?_, fun v => ?_⟩
      · have : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
        rw [smul_smul]
        congr 1
        exact Prod.ext ((zero_mul _).trans this.symm) (one_mul _)
      · convert tmul_mem_latLoc (ha' v) hx using 1
        exact funext fun i => congrArg (compFin F E v) (smul_incl a (x i))
    | zero => exact ⟨smul_zero _, fun v => by
        convert zero_mem (latLoc F Y.L v) using 1
        exact funext fun i => map_zero _⟩
    | add y z _ _ hy hz => exact ⟨by rw [smul_add, hy.1, hz.1], fun v => by
        convert add_mem (hy.2 v) (hz.2 v) using 1
        exact funext fun i => map_add _ _ _⟩
    | neg y _ hy => exact ⟨by rw [smul_neg, hy.1], fun v => by
        convert neg_mem (hy.2 v) using 1
        exact funext fun i => map_neg _ _⟩
  · rintro ⟨h1, h2⟩
    let π := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
    let ι : Af F ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id
    have e1 : ∀ y, ι (π y) = eF F • y := fun y => by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
      | tmul a x => exact congrArg (· ⊗ₜ[F] x) (Prod.ext (zero_mul _).symm (one_mul _).symm)
    have e2 : ∀ v y, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (π y) = compFin F E v y := fun v y => by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a x => rfl
    have e3 : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Y.L : Set (Fin n → E)), ι ∘ y ∈ latHat Y := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨LinearMap.inr F (Ainf F) (Af F) a, map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F),
          ha, x, hx, funext fun i => (smul_incl _ _).symm⟩
      | zero =>
        convert zero_mem (latHat Y) using 1
        exact funext fun i => map_zero _
      | add y z _ _ hy hz =>
        convert add_mem hy hz using 1
        exact funext fun i => map_add _ _ _
      | neg y _ hy =>
        convert neg_mem hy using 1
        exact funext fun i => map_neg _ _
    convert e3 (π ∘ z) ((mem_latHat_iff hL _).2 fun v => by
      convert h2 v using 1
      exact funext fun i => e2 v _) using 1
    exact funext fun i => (congrFun h1 i).symm.trans (e1 _).symm





omit [NumberField E] in
theorem comp_smul (v : Pl F) (a : AF F) (z : AE F E) : compFin F E v (a • z) = evFin F v a ⊗ₜ[F] 1 * compFin F E v z := by
  rw [Algebra.smul_def, map_mul]; rfl

omit [NumberField E] in
theorem comp_eF (v : Pl F) (z : AE F E) : compFin F E v (eF F • z) = compFin F E v z := by
  rw [comp_smul, show evFin F v (eF F) = 1 from map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)]
  exact one_mul _

theorem eF_sq : eF F * eF F = eF F := Prod.ext (zero_mul _) (one_mul _)

theorem mem_intHat (z : AE F E) : eF F • z ∈ intHat F E ↔ ∀ v, compFin F E v z ∈ intLoc F E v := by
  constructor
  · intro h v
    rw [← comp_eF]
    generalize eF F • z = y at h
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, ha, o, rfl⟩ := hy
      rw [smul_incl]
      exact tmul_mem_intLoc (ha v) o
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro h
    let X : Spc F E 1 := ⟨1, stdLattice E 1, fun _ => 1, fun _ => 1⟩
    have key : ∀ y ∈ latHat X, y 0 ∈ intHat F E := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, h1, h2, x, hx, rfl⟩ := hy
        obtain ⟨o, ho⟩ := hx 0 trivial
        exact AddSubgroup.subset_closure ⟨a, h1, h2, o, congrArg (fun t => a • inclR (F := F) (AF F) t) ho.symm⟩
      | zero => exact zero_mem _
      | add y z _ _ hy hz => exact add_mem hy hz
      | neg y _ hy => exact neg_mem hy
    refine key (fun _ => eF F • z) ((mem_latHat (Submodule.fg_pi fun _ => ?_) _).2 ⟨funext fun _ => ?_, fun v => ?_⟩)
    · exact Submodule.fg_range _
    · change eF F • eF F • z = _
      rw [smul_smul, eF_sq]
    · refine mem_latLoc_stdLattice.2 fun _ => ?_
      rw [Function.comp_apply, comp_eF]
      exact h v


end GlobalTheory.ThK.Dbl.Frame

namespace GlobalTheory.ThK.Dbl

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.ThK.Dbl.Frame
open Formalism.UG (bc)


end GlobalTheory.ThK.Dbl

end
