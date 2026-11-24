module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
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
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

theorem GlobalTheory.ArchLineAct.intertwine_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ _hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hWeil γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.lmulL (k := d) (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ X.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ X.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t))) :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)))
    set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let Ru : Matrix (Fin n) (Fin n) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
      { toFun := fun x => x * u, map_add' := fun x y => Matrix.add_mul x y u,
        map_smul' := fun c x => Matrix.smul_mul c x u }
    let K := M.co.e.toLinearMap ∘ₗ Ru
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show mat (γ (Multiplicative.ofAdd (s + t))) * x =
      mat (γ (Multiplicative.ofAdd s)) * (mat (γ (Multiplicative.ofAdd t)) * x)
    rw [ofAdd_add, map_mul, hmat, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show mat (γ (Multiplicative.ofAdd 0)) * x = x
      rw [ofAdd_zero, map_one, hmat1, Matrix.one_mul]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq M.co hu'
    have himpl := hW.impl (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u = L t u := by
      show (mat (γ (Multiplicative.ofAdd t))) * u * ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1ᵀ =
        mat (γ (Multiplicative.ofAdd t)) * u
      rw [show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1 from rfl, Matrix.transpose_one, Matrix.mul_one]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hψ M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hψ M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
