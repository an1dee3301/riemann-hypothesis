module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
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
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
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
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel Matrix

namespace GlobalTheory.IwaPlace

variable {D : D7}

def hermAt (S : HSp D) (x y : Fin S.rank → AE D) : AE D := ∑ i, ∑ j, cA D (y i) * gA S i j * x j

def IsSDAt (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)) : Prop :=
  (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) ∧
    (∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) ∧
    ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ x ∈ Λ, hermAt S y x ∈ intAt D (· = v))

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Mx D V.rank V.rank) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have e1 : ((1 : Mx D V.rank V.rank).map (Ideal.Quotient.mk I)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e2 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (matHom V) g).1 = (mt V g).map (Ideal.Quotient.mk I) := rfl
  constructor
  · intro h i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [e2, Units.val_one] at this
    rw [← e1] at this
    exact this
  · intro h
    ext i j
    rw [e2, Units.val_one, ← e1]
    exact Ideal.Quotient.eq.2 (h i j)

theorem mulVec_mem_idAt {P : Pl D → Prop} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (M *ᵥ y) i ∈ idAt D P :=
  by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {γ : GA D S₀}
    (hγ : γ ∈ grpAt S₀ P) : d.emb0 γ ∈ grpAt S P := by
  have hγ' := (mem_congGrp_iff S₀ (idAt D P) γ).1 hγ
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (d.emb0 γ) - 1 = d.j0 ⬝ (mt S₀ γ - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact hγ' l k)

end GlobalTheory.IwaPlace

end
