module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.VacMove

variable {D : D7}

theorem mt_mul_inv' (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mem_ideal_mul_mul {m n k l : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D))
    (u : Matrix (Fin n) (Fin k) (AE D)) (B : Matrix (Fin k) (Fin l) (AE D)) (hu : ∀ i j, u i j ∈ I) :
    ∀ i j, (A * u * B) i j ∈ I := by
  intro i j
  simp only [Matrix.mul_apply]
  exact I.sum_mem fun x _ => I.mul_mem_right _ (I.sum_mem fun y _ => I.mul_mem_left _ (hu y x))

theorem mem_ideal_mulVec {m n : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D)
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

def pull {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) u) (Formalism.L2.Theta.mt S g)

theorem smul_latV_mem (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a : D.host.E) (ha : a ∈ D.host.AA) :
    ∀ y ∈ GlobalTheory.FinPl.latV S L P, ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ GlobalTheory.FinPl.latA S L P := by
  intro y hy
  have key : GlobalTheory.FinPl.latV S L P ≤ (GlobalTheory.FinPl.latA S L P).comap
      (DistribSMul.toAddMonoidHom (Fin S.rank → AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D)) := by
    unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, b, hb, x, hx, rfl⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    show _ ∈ GlobalTheory.FinPl.latMul S {a | a ∈ D.host.AA} L P
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  exact key hy

theorem mulVec_latA_mem (T : HSp D) (LT MT : Lat T) (P : Pl D → Prop) (h : GA D T) (hMT : IsSelfDualC T MT)
    (hmov : Moves T h LT MT P) : ∀ z ∈ GlobalTheory.FinPl.latA T MT P, Formalism.L2.Theta.mt T h⁻¹ *ᵥ z ∈ GlobalTheory.FinPl.latA T LT P := by
  intro z hz
  have key : GlobalTheory.FinPl.latA T MT P ≤ (GlobalTheory.FinPl.latA T LT P).comap (Matrix.mulVecLin (Formalism.L2.Theta.mt T h⁻¹)).toAddMonoidHom := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    set y' : Fin T.rank → AE D := fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] ((1 : D.host.E) * x i) with hy'def
    have hy' : y' ∈ GlobalTheory.FinPl.latV T MT P := AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, x, hx, rfl⟩
    have hent : ∀ i, y' i ∈ idAt D P := (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 T).2.2.2 MT y' hMT.1).1 hy' |>.1
    have hy'' : Formalism.L2.Theta.mt T h⁻¹ *ᵥ y' ∈ GlobalTheory.FinPl.latV T LT P := by
      rw [hmov _ (mem_ideal_mulVec _ _ _ hent), Matrix.mulVec_mulVec, mt_mul_inv', Matrix.one_mulVec]
      exact hy'
    have hgen : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y' := by
      funext i; simp [y', Algebra.TensorProduct.tmul_mul_tmul]
    show Formalism.L2.Theta.mt T h⁻¹ *ᵥ _ ∈ GlobalTheory.FinPl.latMul T {a | a ∈ D.host.AA} LT P
    rw [hgen, Matrix.mulVec_smul]
    exact smul_latV_mem T LT P a ha _ hy''
  exact key hz

theorem vac_of_moves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (f : WO S T → ℂ), Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f) := by
  intro D ψ S T χS χT om hW LS LT hLS hLT P f hf g h MS MT hMS hMT hmS hmT
  unfold Vac IsLatVac at hf ⊢
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hmem : ∀ u ∈ latO S T (MS : Set _) (MT : Set _) P,
      pull g h u ∈ latO S T (LS : Set _) (LT : Set _) P := by
    intro u hu
    have hu' := (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S T MS MT hMS hMT P u).1 hu
    refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S T LS LT hLS hLT P _).2 ⟨?_, ?_⟩
    · exact mem_ideal_mul_mul (idAt D P) _ _ _ hu'.1
    · intro y hy
      have hent := ((((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 LS y hLS.1).1 hy).1
      have h1 : Formalism.L2.Theta.mt S g *ᵥ y ∈ GlobalTheory.FinPl.latV S MS P := (hmS y hent).1 hy
      have h2 := hu'.2 _ h1
      have h3 := mulVec_latA_mem T LT MT P h hMT hmT _ h2
      show (pull g h u) *ᵥ y ∈ _
      unfold pull
      rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hact : ∀ u : WO S T, actO S T g h (pull g h u) = u := by
    intro u
    unfold actO pull
    simp only [← Matrix.mul_assoc, mt_mul_inv', Matrix.one_mul]
    simp only [Matrix.mul_assoc, mt_mul_inv', Matrix.mul_one]
  have hhalf : ∀ e (u : WO S T), IsHalf e u → IsHalf e (pull g h u) := by
    intro e u hu i j
    unfold pull
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    linear_combination (Formalism.L2.Theta.mt T h⁻¹ i y * Formalism.L2.Theta.mt S g x j) * hu y x
  refine ⟨hW.om_pres (g, h) f hf1, ?_, ?_⟩
  · intro u hu
    have hw := hf2 _ (hmem u hu)
    have e1 := hW.om_heis g h (2 • (pull g h u)) f hf1
    have e2 : actO S T g h (2 • (pull g h u)) = 2 • u := by
      have := hact u
      unfold actO at this ⊢
      rw [two_nsmul, two_nsmul, Matrix.mul_add, Matrix.add_mul, this]
    rw [hw, e2] at e1
    exact e1.symm
  · intro e he u hu hhu
    have hw := hf3 e he _ (hmem u hu) (hhalf e u hhu)
    have e1 := hW.om_heis g h (pull g h u) f hf1
    have e2 : actO S T g h (pull g h u) = u := hact u
    rw [hw, e2] at e1
    exact e1.symm

end GlobalTheory.VacMove

end
