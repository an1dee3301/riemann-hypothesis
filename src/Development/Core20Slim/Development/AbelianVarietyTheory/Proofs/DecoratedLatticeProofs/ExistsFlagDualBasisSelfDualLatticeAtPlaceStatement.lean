module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX * b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := GlobalTheory.IwaFlag.exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2)
      (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol (z : Fin S.rank → D.host.E) (hz : ∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) :
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := by
    have hscale : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [hscale]
    exact hmul _ fun l => GlobalTheory.IwaFlag.mul_incA_mem hεI (hz l)
  have hflag := GlobalTheory.IwaFlag.exists_flag_dual_matrix
    (c := cA D) (O := GlobalTheory.IwaFlag.intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1)
    (fun _ ha _ hb => GlobalTheory.IwaFlag.mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]),
      (FrameLat.cA_int_iff a).2 ha.2⟩)
    (GlobalTheory.IwaFlag.princ_intGrpAt hεε hεc hεI hε ht)
    (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := hflag
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩
