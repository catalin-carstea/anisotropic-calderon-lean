import Calderon.ActualLowerUSSecondRowCoefficients
import Calderon.ActualLowerUSAdjointCoefficients
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.SphereSobolevAngularRaisingThreeHalfGraph

/-!
Finite INPUT dictionaries only; no finite replacement of physical S outputs.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  SpectralCoreRegularity SpectralWeightedGraph SphereHilbertDecomposition AngularShiftGraph
  SphereHarmonic.DegreeGraphLifting ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualCanonicalAngularGainedBracket
  SmoothSphereRotationProjection HarmonicDerivativeOperator

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem finiteCoreSobolevLift_zero_eq (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    finiteCoreSobolevLift hO hD 0 F x = sphereSobolevZeroEquiv hO hD (F.val x) := by
  apply sphereSobolev_ext 0
  intro k
  exact (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD 0 F x k).trans
    (sphereSobolevCoefficientL_zeroEquiv hO hD k (F.val x)).symm

theorem decode_finiteCoreSobolevLift (s : ℝ) (hs : 0 ≤ s)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL s 0 hs (finiteCoreSobolevLift hO hD s F x)) = F.val x := by
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift,
    finiteCoreSobolevLift_zero_eq hO hD F x]
  exact (sphereSobolevZeroEquiv hO hD).symm_apply_apply (F.val x)

theorem halfToSphereL2_finiteCoreSobolevLift
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    sphereSobolevHalfToSphereL2L hO hD (finiteCoreSobolevLift hO hD (1/2 : ℝ) F x) = F.val x :=
  decode_finiteCoreSobolevLift hO hD (1/2 : ℝ) (by norm_num) F x

theorem halfToSphereL2_injective : Function.Injective (sphereSobolevHalfToSphereL2L hO hD) := by
  intro u v h
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  exact (sphereSobolevZeroEquiv hO hD).symm.injective h

theorem degreeHigh_finiteCoreSobolevLift
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) : Half) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreDegree hO hD F) x :=
  (inclusion_finiteCoreSobolevLift_coreDegree hO hD F x).symm.trans
    (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (coreDegree hO hD F) x)

theorem rotationHigh_finiteCoreSobolevLift (i j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (sphereSobolevRotationL (3/2 : ℝ) i j
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) : Half) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreRotation hO hD i j F) x := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  have hIndex : sphereSobolevCoefficientL (1/2 : ℝ) k
      (sphereSobolevRotationL (3/2 : ℝ) i j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
      sphereSobolevCoefficientL ((3/2 : ℝ)-1) k
        (sphereSobolevRotationL (3/2 : ℝ) i j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
      (sphereSobolevRotationL (3/2 : ℝ) i j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)))
      (show (1/2 : ℝ) = (3/2 : ℝ)-1 by norm_num)
  have hLeft := hIndex.trans ((sphereSobolevCoefficientL_rotation (3/2 : ℝ) i j k
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)).trans
      (congrArg (harmonicSphereRotation k i j)
        (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x k)))
  have hCore : sphereHarmonicCoordinate hO hD k ((coreRotation hO hD i j F).val x) =
      harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (F.val x)) :=
    coreBlockOperator_coordinate hO hD (fun n => harmonicSphereRotation n i j) F x k
  exact hLeft.trans ((sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (1/2 : ℝ)
    (coreRotation hO hD i j F) x k).trans hCore).symm

variable (hF : SphereFischerInner)

/-- Actual lowering on a finite physical spectral sum, using only the
selected canonical single-harmonic dictionaries. -/
theorem loweringHigh_coefficient_partialSum (i : Fin 3) (n k : ℕ) (u : Hi) :
    sphereSobolevCoefficientL (1/2 : ℝ) k
      (loweringHigh hF hO hD i (sphereSobolevPartialSum (3/2 : ℝ) n u)) =
      if k+1 < n then harmonicDerivative hF k i
        (sphereSobolevCoefficientL (3/2 : ℝ) (k+1) u) else 0 := by
  have hsingle (m : ℕ) : sphereSobolevCoefficientL (1/2 : ℝ) k
      (loweringHigh hF hO hD i
        (sphereSobolevSingleL (3/2 : ℝ) m (sphereSobolevCoefficientL (3/2 : ℝ) m u))) =
      if m=k+1 then harmonicDerivative hF k i
        (sphereSobolevCoefficientL (3/2 : ℝ) (k+1) u) else 0 := by
    cases m with
    | zero => rw [loweringHigh_single_zero,map_zero]; simp
    | succ m =>
      rw [loweringHigh_single_succ]
      by_cases hm : m=k
      · subst m
        rw [sphereSobolevCoefficientL_single_self]
        simp
      · rw [sphereSobolevCoefficientL_single_ne (1/2 : ℝ) m k (Ne.symm hm)]
        simp only [Nat.succ.injEq,hm,ite_false]
  simp only [sphereSobolevPartialSum,map_sum]
  simp_rw [hsingle]
  simp [Finset.sum_ite_eq',Finset.mem_range]

theorem loweringHigh_finiteCoreSobolevLift (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    loweringHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreDerivative hO hD hF i F) x := by
  obtain ⟨n,hn⟩ := F.property.2.2
  have hPartial : sphereSobolevPartialSum (3/2 : ℝ) n
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      finiteCoreSobolevLift hO hD (3/2 : ℝ) F x := by
    apply sphereSobolev_ext (3/2 : ℝ)
    intro k
    rw [sphereSobolevCoefficientL_partialSum]
    by_cases hk : k<n
    · simp only [hk,ite_true]
    · rw [if_neg hk,sphereSobolevCoefficientL_finiteCoreSobolevLift,
        hn x k (le_of_not_gt hk)]
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  have hNative := coreDerivative_graph hO hD hF i F x k
  calc
    sphereSobolevCoefficientL (1/2 : ℝ) k
        (loweringHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
        sphereSobolevCoefficientL (1/2 : ℝ) k
          (loweringHigh hF hO hD i (sphereSobolevPartialSum (3/2 : ℝ) n
            (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x))) :=
      congrArg (fun z : Hi => sphereSobolevCoefficientL (1/2 : ℝ) k
        (loweringHigh hF hO hD i z)) hPartial.symm
    _ = if k+1<n then harmonicDerivative hF k i
        (sphereHarmonicCoordinate hO hD (k+1) (F.val x)) else 0 := by
      rw [loweringHigh_coefficient_partialSum,sphereSobolevCoefficientL_finiteCoreSobolevLift]
    _ = sphereHarmonicCoordinate hO hD k ((coreDerivative hO hD hF i F).val x) := by
      split_ifs with hk
      · exact hNative.symm
      · rw [hn x (k+1) (le_of_not_gt hk),map_zero] at hNative
        exact hNative.symm
    _ = sphereSobolevCoefficientL (1/2 : ℝ) k
        (finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreDerivative hO hD hF i F) x) :=
      (sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (coreDerivative hO hD hF i F) x k).symm

/-- The selected genuine raising graph gives the partner finite dictionary
needed in weak quadratic telescoping; the input alone is finite. -/
theorem raisingHigh_finiteCoreSobolevLift (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreRaising hO hD hF i F) x := by
  apply halfToSphereL2_injective hO hD
  rw [halfToSphereL2_finiteCoreSobolevLift]
  have hg := sphereSobolevAngularCoordinateTransposeL_threeHalf_raisingGraph hF hO hD i
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
  change ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)),
      sphereSobolevHalfToSphereL2L hO hD
        (raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x))) ∈
      sphereRaisingGraph hF hO hD i at hg
  rw [decode_finiteCoreSobolevLift] at hg
  exact sphereRaisingGraph_output_unique hF hO hD i (F.val x) _ _ hg
    (coreRaising_graph hO hD hF i F x)

theorem loweringHigh_finiteCoreHi_inclusion (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDerivative hO hD hF i F) x) =
      loweringHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (coreDerivative hO hD hF i F) x).trans
      (loweringHigh_finiteCoreSobolevLift hO hD hF i F x).symm

theorem raisingHigh_finiteCoreHi_inclusion (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreRaising hO hD hF i F) x) =
      raisingHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
    (by norm_num) (coreRaising hO hD hF i F) x).trans
      (raisingHigh_finiteCoreSobolevLift hO hD hF i F x).symm

variable (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
  (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

local notation "DF" => nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "DH" => lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p
local notation "DL" => lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD

/-- The exact native lower U-adjoint first coefficient has the chosen physical
high endpoint on the original finite input. All density/raising cancellations
are consumed from the native coefficient dictionary. -/
theorem lowerAdjointFirstHigh_finiteCore_physical (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (DH i x (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) = (DF i F).val x := by
  rw [nativeULowerAdjointFirstCoefficient_eq_full_angular]
  unfold lowerAdjointFirstHigh firstAngularCoefficient firstAngularHigh
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    generatorSharpHigh,generatorHigh,add_apply,smul_apply,sum_apply,
    ContinuousLinearMap.neg_apply,map_add,map_smul,map_sum,map_neg,
    degreeHigh_finiteCoreSobolevLift hO hD,
    rotationHigh_finiteCoreSobolevLift hO hD,
    loweringHigh_finiteCoreSobolevLift hO hD hF,
    sphereSobolevInclusionL_finiteCoreSobolevLift,
    halfToSphereL2_finiteCoreSobolevLift hO hD]
  simp only [nativeReferenceConnectionAction,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.neg_apply,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_add,
    Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,
    Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,Fin.sum_univ_three]
  module

theorem lowerAdjointFirstHigh_finiteCore_graph (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    DH i x (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (DF i F) x := by
  apply halfToSphereL2_injective hO hD
  exact (lowerAdjointFirstHigh_finiteCore_physical hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i F x).trans
    (halfToSphereL2_finiteCoreSobolevLift hO hD (DF i F) x).symm

/-- Physical high/low compatibility for the literal lower-adjoint first map. -/
theorem lowerAdjointFirstHigh_low_compatibility (i : Fin 3) (x : R3) (u : Hi) :
    JL (DH i x u) = DL i x (IH u) := by
  have hG (v : FirstAngularIndex) : JL (firstAngularHigh hF hO hD v u) =
      firstAngularLow hF hO hD v (IH u) := by
    cases v with
    | inl V =>
      cases V with
      | inl bd =>
        have hRot : JL (sphereSobolevRotationL (3/2 : ℝ) bd.1 bd.2 u) =
            sphereSobolevRotationL (1/2 : ℝ) bd.1 bd.2 (IH u) := by
          have hh := congrArg (fun A : Hi →L[ℝ] Neg => A u)
            (sphereSobolevRotationL_threehalf_half_compatibility bd.1 bd.2)
          simpa only [ContinuousLinearMap.comp_apply] using hh
        change JL (-(sphereSobolevRotationL (3/2 : ℝ) bd.1 bd.2 u)) =
          -(sphereSobolevRotationL (1/2 : ℝ) bd.1 bd.2 (IH u))
        exact (map_neg JL _).trans (congrArg (fun z : Neg => -z) hRot)
      | inr z =>
        exact congrArg (fun A : Hi →L[ℝ] Neg => A u) sphereSobolevShiftedDegree_high_half_compatibility
    | inr b => exact v017_inclusion_loweringHigh hF hO hD b u
  simp only [lowerAdjointFirstHigh,lowerAdjointFirstLow,add_apply,smul_apply,sum_apply,
    map_add,map_smul,map_sum]
  simp_rw [hG]

theorem lowerAdjointFirstLow_finiteCore_graph (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    DL i x (finiteCoreSobolevLift hO hD (1/2 : ℝ) F x) =
      finiteCoreSobolevLift hO hD (-(1/2 : ℝ)) (DF i F) x := by
  have hc := lowerAdjointFirstHigh_low_compatibility
    hO hD hF g g2 L q dr Ar p i x (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
  rw [lowerAdjointFirstHigh_finiteCore_graph hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr,
    sphereSobolevInclusionL_finiteCoreSobolevLift,
    sphereSobolevInclusionL_finiteCoreSobolevLift] at hc
  exact hc.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
