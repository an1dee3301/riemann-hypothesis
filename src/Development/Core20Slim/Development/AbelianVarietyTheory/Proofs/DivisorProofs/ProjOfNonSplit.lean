module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Formalism.MainNotions.StandardLattice Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

namespace GlobalTheory.SplitProj

open Filter Topology GlobalTheory.IdemSupport

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

def spl (ε : AE D) : AE D := ε + cA D ε

variable {ε : AE D}

theorem spl_idem (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : spl ε * spl ε = spl ε := by
  obtain ⟨h1, h2, -, -, -⟩ := hε
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  unfold spl
  linear_combination h1 + h3 + 2 * h2

theorem cA_spl (ε : AE D) : cA D (spl ε) = spl ε := by
  unfold spl; rw [RingHom.map_add (f := _), cA_cA, add_comm]

theorem infPart_spl (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : infPart D (spl ε) = 0 := by
  unfold spl
  rw [RingHom.map_add (f := _), (GlobalTheory.IdemSupport.parts_cA ε).1, hε.2.2.1, RingHom.map_zero, add_zero]

theorem spl_mul_split (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {e : AE D} (he : IsSplitIdem D e) :
    spl ε * (e + cA D e) = e + cA D e := by
  have k1 : ∀ x y : AE D, x * y = 0 → cA D x * cA D y = 0 := fun x y h => by
    rw [← RingHom.map_mul, h, RingHom.map_zero]
  have k2 : ∀ x y : AE D, x * y = y → cA D x * cA D y = cA D y := fun x y h => by
    rw [← RingHom.map_mul, h]
  unfold spl
  rcases hε.2.2.2.1 e he with ⟨a, b⟩ | ⟨a, b⟩
  · have c1 := k2 _ _ a
    have c2 := k1 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2
  · have c1 := k1 _ _ a
    have c2 := k2 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2

theorem spl_mul_nonSplit (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hv : NonSplitAt D v η) : spl ε * algebraMap (AF D.host.F) (AE D) η = 0 := by
  have h := hε.2.2.2.2 v η hv
  have h' : algebraMap (AF D.host.F) (AE D) η * cA D ε = 0 := by
    rw [← GlobalTheory.IdemSupport.cA_algebraMap η, ← RingHom.map_mul, h, RingHom.map_zero]
  unfold spl
  linear_combination h + h'

def pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) : GA D V :=
  ⟨piece (spl_idem hε) g.1, piece_mem _ _ (spl_idem hε) (cA_spl ε) g.2⟩

theorem mt_pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) :
    mt V (pc hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

def proj (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) : GA D V →* GA D V :=
  MonoidHom.mk' (pc hε V) fun g h => mt_inj V (by
    simp only [mt_pc, GlobalTheory.IdemSupport.mt_mul]
    rw [mix_mul (spl_idem hε), one_mul])

variable (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {V : HSp D}
include hε

theorem mt_proj (g : GA D V) :
    mt V (proj hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := mt_pc hε V g

theorem proj_eq_self {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = (mt V g - 1) i j) : proj hε V g = g :=
  mt_inj V (by
    rw [mt_proj]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_eq_one {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = 0) : proj hε V g = 1 :=
  mt_inj V (by
    rw [mt_proj, GlobalTheory.IdemSupport.mt_one]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_mem_GfC (g : GA D V) : proj hε V g ∈ GfC V :=
  mem_GfC_of_suppF V (infPart_spl hε) ((suppF_iff V _ _).2 (smul_mix (spl_idem hε) (mt_proj hε g)))

theorem proj_of_suppAt {g : GA D V} (hg : SuppAt ε V g) : proj hε V g = g := proj_eq_self hε hg

theorem proj_of_split {e : AE D} (he : IsSplitIdem D e) {g : GA D V} (hg : SuppAt e V g) : proj hε V g = g :=
  proj_eq_self hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_split hε he]

theorem proj_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (hv : NonSplitAt D v η) {g : GA D V}
    (hg : SuppPl η V g) : proj hε V g = 1 :=
  proj_eq_one hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_nonSplit hε hv, zero_mul]

theorem proj_of_real {g : GA D V} (hg : g ∈ GinfC V) : proj hε V g = 1 := by
  refine proj_eq_one hε fun i j => GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, infPart_spl hε, zero_mul, RingHom.map_zero]) ?_
  have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
  have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
    rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
  have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
  rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]

omit hε in
theorem continuous_mt (V : HSp D) : Continuous fun g : GA D V => mt V g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_proj : Continuous (proj hε V) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have c1 : Continuous fun g => mt V (proj hε V g) := by
    simp only [mt_proj]
    exact ((continuous_mt V).const_smul (spl ε)).add continuous_const
  have c2 : Continuous fun g => mt V (proj hε V g)⁻¹ := by
    simp only [← map_inv]
    exact c1.comp continuous_inv
  exact continuous_iff_continuousAt.2 fun g =>
    GlobalTheory.LocalGlobalChar.tendsto_HA _ _ _ (c1.tendsto g) (c2.tendsto g)

end GlobalTheory.SplitProj
