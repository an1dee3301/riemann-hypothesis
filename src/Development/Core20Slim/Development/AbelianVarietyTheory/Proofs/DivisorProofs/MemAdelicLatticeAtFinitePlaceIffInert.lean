module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSphLat

open GlobalTheory.InertLocField InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_inclR (a : AF F) (e : E) : a • inclR (F := F) (AF F) e = a ⊗ₜ[F] e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem iotaW_toCompl {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (y : Fv F v ⊗[F] E) :
    GlobalTheory.InertBigCell.iotaW hw (toCompl (under_eq_of_isInertAt hw) y) = liftT (E := E) v y := by
  show liftT (E := E) v ((complEquiv hw (under_eq_of_isInertAt hw)).symm
    (complEquiv hw (under_eq_of_isInertAt hw) y)) = liftT (E := E) v y
  rw [RingEquiv.symm_apply_apply]

theorem gen_mem {v : Pl (F := F)} {d : ℕ} (W : Spc F E d) {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F)
    {y : Fin d → E} (hy : y ∈ W.L) :
    (fun i => GlobalTheory.LatVac.liftV v t ⊗ₜ[F] y i) ∈ GlobalTheory.InertSph.latAt W v :=
  AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v t, GlobalTheory.LatVac.at_liftV v t,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ht, y, hy, by funext i; rw [Pi.smul_apply, smul_inclR]⟩

theorem mem_latAt_iff {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ}
    (W : Spc F E d) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ ∃ u ∈ GlobalTheory.LFun.latAt w W.L, z = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := by
  have liftT_tmul (a : Fv F v) (e : E) :
      liftT (E := E) v (a ⊗ₜ[F] e) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] e := rfl
  have h := under_eq_of_isInertAt hw
  let f : (Fin d → w.adicCompletion E) →+ (Fin d → AE F E) :=
    AddMonoidHom.compLeft (GlobalTheory.InertBigCell.iotaW hw) (Fin d)
  have hf : ∀ u, f u = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := fun _ => rfl
  constructor
  · intro hz
    have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.LFun.latAt w W.L).toAddSubgroup.map f := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, haO, y, hy, rfl⟩
      refine ⟨fun i => complMap h (evFin F v a) * algebraMap E _ (y i), ?_, ?_⟩
      · have e1 : (fun i => complMap h (evFin F v a) * algebraMap E (w.adicCompletion E) (y i)) =
            (⟨complMap h (evFin F v a), complMap_mem h haO⟩ : Formalism.UG.Ov E w) •
              (fun i => algebraMap E (w.adicCompletion E) (y i)) := rfl
        rw [Submodule.coe_toAddSubgroup, SetLike.mem_coe, e1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      · funext i
        rw [hf]
        dsimp only
        rw [← toCompl_tmul, iotaW_toCompl, liftT_tmul, ← eq_liftV_of_at v ha, Pi.smul_apply, smul_inclR]
    obtain ⟨u, hu, e⟩ := AddSubgroup.mem_map.1 (hle hz)
    exact ⟨u, hu, e.symm⟩
  · rintro ⟨u, hu, rfl⟩
    have key : ∀ u ∈ GlobalTheory.LFun.latAt w W.L, ∀ o : Formalism.UG.Ov E w, f (o • u) ∈ GlobalTheory.InertSph.latAt W v := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        intro o
        obtain ⟨t, ht⟩ := toCompl_surjective h (o : w.adicCompletion E)
        have htI : t ∈ intLoc F E v := (mem_intLoc_iff hw h t).2 (ht ▸ o.2)
        have e1 : f (o • fun i => algebraMap E (w.adicCompletion E) (y i)) =
            fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i)) := by
          funext i
          rw [hf]
          dsimp only
          rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, ← ht,
            show algebraMap E (w.adicCompletion E) (y i) = toCompl h ((1 : Fv F v) ⊗ₜ[F] y i) by
              rw [toCompl_tmul, map_one, one_mul], ← map_mul, iotaW_toCompl]
        rw [e1]
        refine intLoc_induction (p := fun t => (fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i))) ∈
          GlobalTheory.InertSph.latAt W v) (fun a ha x => ?_) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) htI
        · convert gen_mem W ha (W.L.smul_mem x hy) using 1
          funext i
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, liftT_tmul, Pi.smul_apply, Algebra.smul_def]
        · convert (zero_mem (GlobalTheory.InertSph.latAt W v)) using 1
          funext i
          simp
        · convert add_mem hp hq using 1
          funext i
          simp [add_mul, map_add (f := _)]
        · convert neg_mem hp using 1
          funext i
          simp [neg_mul, map_neg]
      | zero => intro o; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro o; rw [smul_add, map_add (f := _)]; exact add_mem (hx o) (hy o)
      | smul a x _ hx => intro o; rw [smul_smul]; exact hx (o * a)
    have := key u hu 1
    rw [one_smul] at this
    exact this

end GlobalTheory.InertSphLat
