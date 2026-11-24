module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDecomp

variable {D : D7}

theorem adj_eq' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := rfl

theorem frame_relations {V V' : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    adj D C' * V.gram * C = 1 ∧ (V'.gram⁻¹ * adj D B * V.gram) * C = 0 ∧
    (V'.gram⁻¹ * adj D B * V.gram) * C' = 0 ∧ (V'.gram⁻¹ * adj D B * V.gram) * B = 1 ∧
    adj D C * V.gram * C = 0 ∧
    C * (adj D C' * V.gram) + (B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram)) = 1 := by
  have hG : V.gramᴴ = V.gram := GlobalTheory.MixModel.gram_conjTranspose V
  have hC : Cᴴ * V.gram * C = 0 := by
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C = Cᴴ := adj_eq' C
    have := hs.frame.2.2
    rwa [e] at this
  have hB := hs.isom
  have hCB := hs.orth
  simp only [adj_eq'] at hB hCB h1 h2 h3 ⊢

  have hC'C : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose hCB
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hG' : V'.gram⁻¹ * V'.gram = 1 := Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V')
  have hPC : V'.gram⁻¹ * Bᴴ * V.gram * C = 0 := by
    simp only [Matrix.mul_assoc] at hBC ⊢; rw [hBC, Matrix.mul_zero]
  have hPC' : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0 := by
    simp only [Matrix.mul_assoc] at hBC' ⊢; rw [hBC', Matrix.mul_zero]
  have hPB : V'.gram⁻¹ * Bᴴ * V.gram * B = 1 := by
    simp only [Matrix.mul_assoc] at hB ⊢; rw [hB, hG']
  refine ⟨hC'C, hPC, hPC', hPB, hC, ?_⟩

  set P := V'.gram⁻¹ * Bᴴ * V.gram with hP
  let M : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E := Matrix.fromCols C (Matrix.fromCols B C')
  let N : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows (C'ᴴ * V.gram) (Matrix.fromRows P (Cᴴ * V.gram))
  have hNM : N * M = 1 := by
    simp only [N, M, Matrix.fromRows_mul, Matrix.mul_fromCols]
    ext (i | i | i) (j | j | j) <;>
      simp [hC'C, hPC, hPC', hPB, hC, h1, h2, h3, hCB, Matrix.one_apply]
  have hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have := hs.rank
    omega
  have hMN : M * N = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hNM
  simpa [M, N, Matrix.fromCols_mul_fromRows] using hMN


set_option maxHeartbeats 1000000 in
theorem decomp_exists : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  intro D V V' W r C B hs C' h1 h2 h3
  obtain ⟨hC'C, hPC, hPC', hPB, hCC, hid⟩ := frame_relations hs h1 h2 h3
  have hV'r := GlobalTheory.MixModel.ratL_eq W V'
  have hVr := GlobalTheory.MixModel.ratL_eq W V

  set f := incA D with hf
  set a := (adj D C' * V.gram).map f with ha
  set c := (adj D C * V.gram).map f with hc
  set p := (V'.gram⁻¹ * adj D B * V.gram).map f with hp
  set u := C.map f with hu
  set u' := C'.map f with hu'
  set b := B.map f with hb
  have m1 : ∀ {k l m : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E) (Y : Matrix (Fin l) (Fin m) D.host.E),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul).symm
  have z0 : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) D.host.E).map f = 0 := Matrix.map_zero _ (map_zero f)
  have o1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) D.host.E).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have au : a * u = 1 := by rw [ha, hu, m1, hC'C, o1]
  have cu : c * u = 0 := by rw [hc, hu, m1, hCC, z0]
  have pu : p * u = 0 := by rw [hp, hu, m1, hPC, z0]
  have au' : a * u' = 0 := by rw [ha, hu', m1, h2, z0]
  have cu' : c * u' = 1 := by rw [hc, hu', m1, h1, o1]
  have pu' : p * u' = 0 := by rw [hp, hu', m1, hPC', z0]
  have ab : a * b = 0 := by rw [ha, hb, m1, h3, z0]
  have cb : c * b = 0 := by rw [hc, hb, m1, hs.orth, z0]
  have pb : p * b = 1 := by rw [hp, hb, m1, hPB, o1]
  have key : u * a + (b * p + u' * c) = 1 := by
    rw [ha, hc, hp, hu, hu', hb, m1, m1, m1, ← Matrix.map_add f (map_add f), ← Matrix.map_add f (map_add f), hid, o1]

  have fwd : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      isoPart V W C' t + isoPart V W C y + midPart V V' W B x = t * a + y * c + x * p := fun _ _ _ => rfl
  have back : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      (t * a + y * c + x * p) * u = t ∧ (t * a + y * c + x * p) * u' = y ∧
        (t * a + y * c + x * p) * b = x := by
    intro t y x
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Matrix.add_mul, Matrix.mul_assoc, au, cu, pu, au', cu', pu', ab, cb, pb, Matrix.mul_one,
        Matrix.mul_zero, add_zero, zero_add]
  have cont : ∀ {k l m : ℕ} (Q : Mx D l m), Continuous fun z : Mx D k l => z * Q := by
    intro k l m Q
    exact continuous_id.matrix_mul continuous_const
  haveI := (GlobalTheory.MixModel.lattice_Mx D W.rank V.rank).1
  let e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W :=
    { toFun := fun q => isoPart V W C' q.1 + isoPart V W C q.2.1 + midPart V V' W B q.2.2
      invFun := fun w => (w * u, w * u', w * b)
      left_inv := by
        rintro ⟨t, y, x⟩
        simp only [fwd]
        rw [(back t y x).1, (back t y x).2.1, (back t y x).2.2]
      right_inv := by
        intro w
        simp only [fwd]
        calc w * u * a + w * u' * c + w * b * p = w * (u * a + (b * p + u' * c)) := by
              simp only [Matrix.mul_add, Matrix.mul_assoc]; abel
          _ = w := by rw [key, Matrix.mul_one]
      map_add' := by
        rintro ⟨t, y, x⟩ ⟨t', y', x'⟩
        simp only [fwd, Prod.mk_add_mk, Matrix.add_mul]
        abel
      continuous_toFun := by
        simp only [fwd]
        exact (((cont a).comp continuous_fst).add ((cont c).comp (continuous_fst.comp continuous_snd))).add
          ((cont p).comp (continuous_snd.comp continuous_snd))
      continuous_invFun := ((cont u).prodMk ((cont u').prodMk (cont b))) }
  refine ⟨e, fun t y x => rfl, fun t y x => ?_⟩
  change isoPart V W C' t + isoPart V W C y + midPart V V' W B x ∈ ratL W V ↔ _
  rw [fwd, hVr, hV'r]
  have hr : ∀ {k l : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E), X.map f ∈ GlobalTheory.MixModel.ratMx D k l :=
    fun X => GlobalTheory.MixModel.rat_mem X
  have hmul : ∀ {k l m : ℕ} {X : Mx D k l} {Y : Mx D l m},
      X ∈ GlobalTheory.MixModel.ratMx D k l → Y ∈ GlobalTheory.MixModel.ratMx D l m →
      X * Y ∈ GlobalTheory.MixModel.ratMx D k m := by
    intro k l m X Y hX hY
    obtain ⟨A, rfl⟩ := hX
    obtain ⟨B, rfl⟩ := hY
    change A.map f * B.map f ∈ GlobalTheory.MixModel.ratMx D k m
    rw [m1]
    exact hr (A * B)
  constructor
  · intro h
    obtain ⟨b1, b2, b3⟩ := back t y x
    refine ⟨?_, ?_, ?_⟩
    · rw [← b1]; exact hmul h (hr C)
    · rw [← b2]; exact hmul h (hr C')
    · rw [← b3]; exact hmul h (hr B)
  · rintro ⟨ht, hy, hx⟩
    exact add_mem (add_mem (hmul ht (hr _)) (hmul hy (hr _)))
      (hmul hx (hr _))

end GlobalTheory.TwistDecomp

end
