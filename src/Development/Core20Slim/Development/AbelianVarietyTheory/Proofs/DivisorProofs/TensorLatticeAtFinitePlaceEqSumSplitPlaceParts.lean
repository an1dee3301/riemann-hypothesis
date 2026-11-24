module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LatSplit

open GlobalTheory.AdelicU.Supp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleTens_tmul (v : Pl (F := F)) (a : Fv F v) (x : E) :
    singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] x := rfl

theorem tmul_smul_gen_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) {c : AF F} (hc : At (evFin F v) c)
    (hcv : evFin F v c ∈ v.adicCompletionIntegers F) {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → E} (hy : y ∈ W.L) :
    singleTens E v (a ⊗ₜ[F] (o : E)) • (c • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v := by
  refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, ?_⟩
  · intro u hu
    rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
    exact mul_mem ha hcv
  · ext i j
    simp only [singleTens_tmul, Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Pi.smul_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, inclR]
    change _ * ((c ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] (x i * y j))) =
      ((GlobalTheory.LatVac.liftV v a * c) ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] ((o:E) * x i * y j))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

theorem singleTens_smul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fv F v ⊗[F] E}
    (hy : y ∈ intLoc F E v) {γ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hγ : γ ∈ latAtV X W v) :
    singleTens E v y • γ ∈ latAtV X W v := by
  refine intLoc_induction (p := fun y => singleTens E v y • γ ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
  · intro a ha o
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, hcv, x, hx, y', hy', rfl⟩ := hz
      exact tmul_smul_gen_mem X W v ha o hc hcv hx hy'
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  · show singleTens E v 0 • γ ∈ latAtV X W v
    rw [map_zero, zero_smul]; exact zero_mem _
  · intro y z h h'
    show singleTens E v (y + z) • γ ∈ latAtV X W v
    rw [map_add (f := _), add_smul]; exact add_mem h h'
  · intro y h
    show singleTens E v (-y) • γ ∈ latAtV X W v
    rw [map_neg, neg_smul]; exact neg_mem h

theorem piW_splitIdemAd {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) :
    piW t (splitIdemAd hcm t) = 1 ∧ piW (t.comp σ) (splitIdemAd hcm t) = 0 := by
  constructor
  · change splitProj t (compFin F E v (singleTens E v (splitIdem hcm t))) = 1
    rw [compFin_singleTens_self, splitProj_splitIdem]
  · change splitProj (t.comp σ) (compFin F E v (singleTens E v (splitIdem hcm t))) = 0
    rw [compFin_singleTens_self, splitProj_comp_splitIdem]

theorem latAtV_decomp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  intro F E _ _ _ _ _ σ n d hcm X W v t γ hγ
  have h1 : splitIdemAd hcm t • γ ∈ latAtV X W v := singleTens_smul_mem X W v (splitIdem_mem hcm t) hγ
  obtain ⟨e1, e0⟩ := piW_splitIdemAd hcm t
  refine ⟨splitIdemAd hcm t • γ, h1, γ - splitIdemAd hcm t • γ, sub_mem hγ h1, (add_sub_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [smul_eq_mul, e0]
  · ext i j
    simp [smul_eq_mul, e1]

end GlobalTheory.LatSplit
