import Calderon.ActualReferenceCutoffCommutatorEnergy
import Calderon.ActualNativeCoverScalarCutoffGraph
import Calderon.ActualReferenceProfileEnergyFiniteSum
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral
import Calderon.WeightedBaseSpectral

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace BigOperators
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth RadiusProfile
  ReferenceWeightedApproximation ReferenceDensityBounds WeightedBaseSpectral

attribute [local irreducible] finiteCoreReferenceProfileEnergy finiteCoreSobolevLift
  referenceDensityScalarCutoffCommutator actualReferenceBeta referenceRadius
  nativePacketPhysicalDensityOperator sphereSobolevInclusionL sphereSobolevZeroEquiv

private lemma self_le_ten_thousand_eighth (M : ℝ) (hM : 1 ≤ M) :
    M ≤ 10000*M^8 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have h7 : 1 ≤ M^7 := one_le_pow₀ hM
  calc
    M = M*1 := by ring
    _ ≤ M*M^7 := mul_le_mul_of_nonneg_left h7 hM0
    _ = M^8 := by ring
    _ ≤ 10000*M^8 := by nlinarith only [pow_nonneg hM0 8]

private lemma localization_norm_add_sq_le
    {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have hTriangle : ‖a+b‖ ≤ ‖a‖+‖b‖ := norm_add_le a b
  have hSquare : ‖a+b‖^2 ≤ (‖a‖+‖b‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hTriangle
  have hScalar : (‖a‖+‖b‖)^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
    nlinarith only [sq_nonneg (‖a‖-‖b‖)]
  exact hSquare.trans hScalar

private lemma localization_partition_perturbation_sum_le
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (theta : ι → ℝ) (v : E) (c : ι → E)
    (hTheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ 1) (hSum : (∑ i, theta i) ≤ 1) :
    (∑ i, ‖theta i • v+c i‖^2) ≤ 2*‖v‖^2+2*∑ i, ‖c i‖^2 := by
  classical
  have hThetaSquare (i : ι) : (theta i)^2 ≤ theta i := by
    nlinarith only [mul_nonneg (hTheta i).1 (sub_nonneg.mpr (hTheta i).2)]
  have hTerm (i : ι) :
      ‖theta i • v+c i‖^2 ≤ 2*theta i*‖v‖^2+2*‖c i‖^2 := by
    have hNorm : ‖theta i • v‖^2 = (theta i)^2*‖v‖^2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hTheta i).1]
      ring
    calc
      ‖theta i • v+c i‖^2 ≤ 2*‖theta i • v‖^2+2*‖c i‖^2 :=
        localization_norm_add_sq_le _ _
      _ = 2*((theta i)^2*‖v‖^2)+2*‖c i‖^2 := by rw [hNorm]
      _ ≤ 2*(theta i*‖v‖^2)+2*‖c i‖^2 := add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hThetaSquare i) (sq_nonneg _)) (by norm_num)) le_rfl
      _ = 2*theta i*‖v‖^2+2*‖c i‖^2 := by ring
  calc
    (∑ i, ‖theta i • v+c i‖^2) ≤ ∑ i, (2*theta i*‖v‖^2+2*‖c i‖^2) :=
      Finset.sum_le_sum (fun i _ => hTerm i)
    _ = 2*(∑ i, theta i)*‖v‖^2+2*∑ i, ‖c i‖^2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2*1*‖v‖^2+2*∑ i, ‖c i‖^2 := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSum (by norm_num))
        (sq_nonneg _)) le_rfl
    _ = 2*‖v‖^2+2*∑ i, ‖c i‖^2 := by ring

/-- Common actual finite-cover cutoff coefficient chosen before every late profile/input. -/
theorem exists_native_cover_scalar_cutoff_commutator_referenceProfileEnergy_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ) (hL : 0 < L)
    (cover : NativeNormalCover S L)
    (theta : Fin cover.count → R3 → ℝ) (hTheta : ∀ i, ContDiff ℝ ∞ (theta i))
    (hThetaSupport : ∀ i, tsupport (theta i) ⊆ (cover.packet i).centers) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ betaFloor : ℝ, 1 ≤ betaFloor → ∀ p : ℕ, 1 ≤ p →
      ∀ q ∈ Icc (0 : ℝ) cover.dilationCeiling,
      ∀ delta Rstar : ℝ, 0 < delta → 0 < Rstar →
      let R := referenceRadius delta Rstar p L
      let beta := actualReferenceBeta S.g1 L q delta Rstar p
      (∀ x ∈ cylinder, betaFloor ≤ beta x ∧ ‖fderiv ℝ R x‖ ≤ 1 ∧
        R x*(beta x)^2 ≤ 1 ∧ R x < cover.radiusCeiling) →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ interior cylinder →
      let E := fun x : R3 => finiteCoreReferenceProfileEnergy hO hD S.g1 S.g1_admissible
        L q (beta x) F x
      let Ccut := fun (i : Fin cover.count) (x : R3) =>
        nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p
          (theta i) F i x
      (∀ i x, ‖Ccut i x‖^2 ≤ (10000*M^8/beta x)*E x) ∧
      (∀ i x, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2 ≤
        (10000*M^8/betaFloor)*(referenceDensityFamily S.g1 L (q,x)*E x)) ∧
      (∀ i, Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2)
        (volume : Measure R3) ∧
        (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) ≤
          (10000*M^8/betaFloor)*(∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E x)) ∧
      (∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) ≤
        ((cover.count : ℝ)*10000*M^8/betaFloor)*
          (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E x) := by
  classical
  have hCoefficients (i : Fin cover.count) :=
    exists_referenceDensityScalarCutoffCommutator_referenceProfileEnergy_bound
      S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
      (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
      (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
      S.g1_admissible hcalc hF hO hD tau0 hreg S.g2 S.g2_admissible (theta i) (hTheta i)
  choose Ccoef hCcoef hLocal using hCoefficients
  let M : ℝ := max 1 (∑ i, Ccoef i)
  let Q : ℝ := 10000*M^8
  have hM : 1 ≤ M := le_max_left _ _
  have hQ0 : 0 ≤ Q := mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hM) 8)
  have hCoef (i : Fin cover.count) : Ccoef i ≤ Q := by
    have hSum : Ccoef i ≤ ∑ j, Ccoef j :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hCcoef j)) (Finset.mem_univ i)
    exact hSum.trans ((le_max_right _ _).trans (self_le_ten_thousand_eighth M hM))
  refine ⟨M, hM, ?_⟩
  intro betaFloor hFloor p hp q hq delta Rstar hd hRs
  dsimp only
  intro hProfile F hFS
  let R := referenceRadius delta Rstar p L
  let beta := actualReferenceBeta S.g1 L q delta Rstar p
  let E : R3 → ℝ := fun x => finiteCoreReferenceProfileEnergy hO hD S.g1 S.g1_admissible
    L q (beta x) F x
  let Ccut : Fin cover.count → R3 → SphereL2 := fun i x =>
    nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p
      (theta i) F i x
  have hR : ContDiff ℝ ∞ R := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hBetaPositive (x : R3) : 0 < beta x :=
    actualReferenceBeta_pos S.g1 S.g1_admissible L q delta Rstar p hL hd hRs hp x
  have hBetaContinuous : Continuous beta :=
    continuous_actualReferenceBeta S.g1 S.g1_admissible L q delta Rstar p hL hd hRs
  have hENonneg (x : R3) : 0 ≤ E x :=
    finiteCoreReferenceProfileEnergy_nonneg hO hD S.g1 S.g1_admissible L q
      (beta x) (hBetaPositive x).le F x
  have hDensityNonneg (x : R3) : 0 ≤ referenceDensityFamily S.g1 L (q,x) :=
    (referenceDensityFamily_pos S.g1 S.g1_admissible L (q,x)).le
  have hRadius : ∀ x ∈ cylinder, R x < cover.radiusCeiling :=
    fun x hx => (hProfile x hx).2.2.2
  have hData (i : Fin cover.count) := nativePacketScalarCutoffCommutatorL2_smooth_support
    hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hd hRs hq hRadius
      i (theta i) (hTheta i) (hThetaSupport i) F hFS
  have hSupport (i : Fin cover.count) : tsupport (Ccut i) ⊆ tsupport (theta i) ∩ tsupport F.val :=
    (hData i).2.2
  have hqOne : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans cover.dilation_le_one⟩
  have hPoint (i : Fin cover.count) (x : R3) : ‖Ccut i x‖^2 ≤ (Q/beta x)*E x := by
    by_cases hx : x ∈ tsupport (Ccut i)
    · have hs := hSupport i hx
      have hxCylinder : x ∈ cylinder := interior_subset (hFS hs.2)
      have hxCenter := hThetaSupport i hs.1
      have hxRoom : ‖x-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho :=
        ((cover.packet i).centers_room x hxCenter).1.le
      have hrRoom : R x ≤ 4*(cover.packet i).rho :=
        ((hProfile x hxCylinder).2.2.2.trans (cover.radius_room i)).le
      have hHalf : ‖nativePacketScalarCutoffCommutatorHalf hcalc hF hO hD tau0 S L cover
          q delta Rstar p (theta i) F i x‖^2 ≤ (Ccoef i/beta x)*E x :=
        hLocal i q hqOne R x hxRoom (hR.differentiable (by simp) x)
          (referenceRadius_pos delta Rstar p L x hd hRs) hrRoom (hProfile x hxCylinder).2.1
          (beta x) (hFloor.trans (hProfile x hxCylinder).1) (hProfile x hxCylinder).2.2.1 F
      have hContract : ‖Ccut i x‖ ≤
          ‖nativePacketScalarCutoffCommutatorHalf hcalc hF hO hD tau0 S L cover
            q delta Rstar p (theta i) F i x‖ :=
        norm_sphereSobolevHalfToSphereL2L_apply_le hO hD _
      have hSquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hContract
      exact hSquare.trans (hHalf.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hCoef i) (hBetaPositive x).le) (hENonneg x)))
    · have hz : Ccut i x = 0 := image_eq_zero_of_notMem_tsupport hx
      calc
        ‖Ccut i x‖^2 = 0 := by rw [hz, norm_zero]; norm_num
        _ ≤ (Q/beta x)*E x := mul_nonneg
          (div_nonneg hQ0 (hBetaPositive x).le) (hENonneg x)
  have hWeighted (i : Fin cover.count) (x : R3) :
      referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2 ≤
        (Q/betaFloor)*(referenceDensityFamily S.g1 L (q,x)*E x) := by
    have hNorm : ‖Ccut i x‖^2 ≤ (Q/betaFloor)*E x := by
      by_cases hx : x ∈ tsupport (Ccut i)
      · have hxCylinder : x ∈ cylinder := interior_subset (hFS (hSupport i hx).2)
        exact (hPoint i x).trans (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hQ0 (zero_lt_one.trans_le hFloor)
            (hProfile x hxCylinder).1) (hENonneg x))
      · have hz : Ccut i x = 0 := image_eq_zero_of_notMem_tsupport hx
        calc
          ‖Ccut i x‖^2 = 0 := by rw [hz, norm_zero]; norm_num
          _ ≤ (Q/betaFloor)*E x := mul_nonneg
            (div_nonneg hQ0 (zero_le_one.trans hFloor)) (hENonneg x)
    exact (mul_le_mul_of_nonneg_left hNorm (hDensityNonneg x)).trans_eq (by ring)
  have hEInt : Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*E x) :=
    integrable_finiteCoreReferenceProfileEnergy hO hD S.g1 S.g1_admissible L q beta
      hBetaContinuous hBetaPositive F
  have hIntegrals (i : Fin cover.count) :
      Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) ∧
      (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) ≤
        (Q/betaFloor)*(∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E x) := by
    have hInt : Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) :=
      integrable_referenceBase_norm_sq S.g1 S.g1_admissible L q (Ccut i)
        (hData i).1.continuous (hData i).2.1
    exact ⟨hInt, (integral_mono hInt (hEInt.const_mul (Q/betaFloor))
      (hWeighted i)).trans_eq (integral_const_mul _ _)⟩
  refine ⟨hPoint, hWeighted, hIntegrals, ?_⟩
  calc
    (∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) ≤
        ∑ _i : Fin cover.count, (Q/betaFloor)*
          (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E x) :=
      Finset.sum_le_sum (fun i _ => (hIntegrals i).2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [Q]
      ring

/-- Early partition and actual all-cover localized full outputs with their original energy costs. -/
theorem exists_native_cover_partition_physical_output_referenceProfileEnergy_bounds
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel tau0)
    (S : KnownSideSourceData) (L : ℝ) (hL : 0 < L) (cover : NativeNormalCover S L)
    (hCenter : ∀ i : Fin cover.count, ∀ x ∈ (cover.packet i).centers,
      ‖x-(cover.packet i).y0‖ < (cover.packet i).rho) :
    ∃ (theta : Fin cover.count → R3 → ℝ) (hTheta : ∀ i, ContDiff ℝ ∞ (theta i)) (M : ℝ),
      1 ≤ M ∧ (∀ i x, 0 ≤ theta i x ∧ theta i x ≤ 1) ∧
      (∀ x ∈ cylinder, ∑ i, theta i x = 1) ∧ (∀ x : R3, ∑ i, theta i x ≤ 1) ∧
      (∀ i, tsupport (theta i) ⊆ (cover.packet i).centers) ∧
      (∀ i, HasCompactSupport (theta i)) ∧
      (∀ i, IsCompact (tsupport (theta i) ∩ cylinder) ∧
        tsupport (theta i) ∩ cylinder ⊆ Metric.ball (cover.packet i).y0 (cover.packet i).rho) ∧
      ∀ betaFloor : ℝ, 1 ≤ betaFloor → ∀ p : ℕ, 1 ≤ p →
      ∀ q ∈ Icc (0 : ℝ) cover.dilationCeiling,
      ∀ delta Rstar : ℝ, 0 < delta → 0 < Rstar →
      let R := referenceRadius delta Rstar p L
      let beta := actualReferenceBeta S.g1 L q delta Rstar p
      (∀ x ∈ cylinder, betaFloor ≤ beta x ∧ ‖fderiv ℝ R x‖ ≤ 1 ∧
        R x*(beta x)^2 ≤ 1 ∧ R x < cover.radiusCeiling) →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ interior cylinder →
      ∀ V : R3 → SphereL2, ContDiff ℝ ∞ V → tsupport V ⊆ interior cylinder →
      (∀ j : Fin cover.count, ∀ x ∈ interior cylinder ∩ (cover.packet j).centers,
        sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V x)) =
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) j x) →
      let Fi := fun i : Fin cover.count => coreScalar hO hD (theta i) (hTheta i) F
      let Wi := fun (i : Fin cover.count) (x : R3) => theta i x • V x +
        nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p
          (theta i) F i x
      let E := fun (G : smoothCompactFiniteSphereCore hO hD) (x : R3) =>
        finiteCoreReferenceProfileEnergy hO hD S.g1 S.g1_admissible L q (beta x) G x
      (∀ i, ContDiff ℝ ∞ (Wi i) ∧ HasCompactSupport (Wi i) ∧
        tsupport (Wi i) ⊆ tsupport (theta i) ∩ tsupport F.val ∧
        ∀ j : Fin cover.count, ∀ x ∈ interior cylinder ∩ (cover.packet j).centers,
          sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
            (sphereSobolevZeroEquiv hO hD (Wi i x)) =
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2 : ℝ) (Fi i)) j x) ∧
      (∀ i, Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2)
        (volume : Measure R3)) ∧
      (∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2) ≤
        2*(∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖V x‖^2) +
        (2*(cover.count : ℝ)*10000*M^8/betaFloor)*
          (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E F x) ∧
      (∀ x : R3, E F x ≤ (cover.count : ℝ)*∑ i, E (Fi i) x) ∧
      (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E F x) ≤
        (cover.count : ℝ)*∑ i : Fin cover.count,
          ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E (Fi i) x := by
  classical
  obtain ⟨theta, hTheta, hThetaBounds, hPartition, hSum, hThetaSupport, hThetaCompact, hK⟩ :=
    exists_native_cover_smooth_partition S L cover hCenter
  obtain ⟨M, hM, hBound⟩ :=
    exists_native_cover_scalar_cutoff_commutator_referenceProfileEnergy_bound
      hcalc hreg hF hO hD tau0 S L hL cover theta hTheta hThetaSupport
  refine ⟨theta, hTheta, M, hM, hThetaBounds, hPartition, hSum, hThetaSupport,
    hThetaCompact, hK, ?_⟩
  intro betaFloor hFloor p hp q hq delta Rstar hd hRs
  dsimp only
  intro hProfile F hFS V hV hVS hGraph
  let beta := actualReferenceBeta S.g1 L q delta Rstar p
  let Q : ℝ := 10000*M^8
  let Fi : Fin cover.count → smoothCompactFiniteSphereCore hO hD :=
    fun i => coreScalar hO hD (theta i) (hTheta i) F
  let Ccut : Fin cover.count → R3 → SphereL2 := fun i x =>
    nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p
      (theta i) F i x
  let Wi : Fin cover.count → R3 → SphereL2 := fun i x => theta i x • V x+Ccut i x
  let E : smoothCompactFiniteSphereCore hO hD → R3 → ℝ := fun G x =>
    finiteCoreReferenceProfileEnergy hO hD S.g1 S.g1_admissible L q (beta x) G x
  have hBetaPositive (x : R3) : 0 < beta x :=
    actualReferenceBeta_pos S.g1 S.g1_admissible L q delta Rstar p hL hd hRs hp x
  have hBetaContinuous : Continuous beta :=
    continuous_actualReferenceBeta S.g1 S.g1_admissible L q delta Rstar p hL hd hRs
  have hDensityNonneg (x : R3) : 0 ≤ referenceDensityFamily S.g1 L (q,x) :=
    (referenceDensityFamily_pos S.g1 S.g1_admissible L (q,x)).le
  have hRadius : ∀ x ∈ cylinder, referenceRadius delta Rstar p L x < cover.radiusCeiling :=
    fun x hx => (hProfile x hx).2.2.2
  have hWData (i : Fin cover.count) := native_cover_scalar_cutoff_output_graph
    hcalc hreg hF hO hD tau0 hKernel S L q delta Rstar p cover hd hRs hq hRadius
      i (theta i) (hTheta i) (hThetaSupport i) F hFS V hV hVS hGraph
  have hWiInt (i : Fin cover.count) :
      Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2) :=
    integrable_referenceBase_norm_sq S.g1 S.g1_admissible L q (Wi i)
      (hWData i).1.continuous (hWData i).2.1
  have hVCompact : HasCompactSupport V :=
    isCompact_native_center_cylinder.of_isClosed_subset (isClosed_tsupport V)
      (fun x hx => interior_subset (hVS hx))
  have hVInt : Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*‖V x‖^2) :=
    integrable_referenceBase_norm_sq S.g1 S.g1_admissible L q V hV.continuous hVCompact
  have hCData := hBound betaFloor hFloor p hp q hq delta Rstar hd hRs hProfile F hFS
  have hCInt (i : Fin cover.count) :
      Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) :=
    (hCData.2.2.1 i).1
  have hCSum :
      (∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) ≤
      ((cover.count : ℝ)*Q/betaFloor)*
        (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E F x) := by
    simpa only [Q, mul_assoc] using hCData.2.2.2
  have hWSumInt : Integrable (fun x : R3 =>
      ∑ i : Fin cover.count, referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2) :=
    integrable_finsetSum _ (fun i _ => hWiInt i)
  have hCSumInt : Integrable (fun x : R3 =>
      ∑ i : Fin cover.count, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) :=
    integrable_finsetSum _ (fun i _ => hCInt i)
  have hCostPoint (x : R3) :
      (∑ i : Fin cover.count, referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2) ≤
        2*(referenceDensityFamily S.g1 L (q,x)*‖V x‖^2)+
          2*∑ i : Fin cover.count, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2 := by
    have hNorm := localization_partition_perturbation_sum_le
      (fun i => theta i x) (V x) (fun i => Ccut i x) (fun i => hThetaBounds i x) (hSum x)
    calc
      _ = referenceDensityFamily S.g1 L (q,x)*(∑ i : Fin cover.count, ‖Wi i x‖^2) := by
        rw [Finset.mul_sum]
      _ ≤ referenceDensityFamily S.g1 L (q,x)*
          (2*‖V x‖^2+2*∑ i : Fin cover.count, ‖Ccut i x‖^2) :=
        mul_le_mul_of_nonneg_left hNorm (hDensityNonneg x)
      _ = 2*(referenceDensityFamily S.g1 L (q,x)*‖V x‖^2)+
          2*(referenceDensityFamily S.g1 L (q,x)*∑ i : Fin cover.count, ‖Ccut i x‖^2) := by ring
      _ = _ := by rw [Finset.mul_sum]
  have hRawCost :
      (∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2) ≤
        2*(∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖V x‖^2)+
          2*∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2 := by
    calc
      _ = ∫ x : R3, ∑ i : Fin cover.count,
          referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2 :=
        (integral_finsetSum Finset.univ (fun i _ => hWiInt i)).symm
      _ ≤ ∫ x : R3, (2*(referenceDensityFamily S.g1 L (q,x)*‖V x‖^2)+
          2*∑ i : Fin cover.count, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2) :=
        integral_mono hWSumInt ((hVInt.const_mul 2).add (hCSumInt.const_mul 2)) hCostPoint
      _ = _ := by
        rw [integral_add (hVInt.const_mul 2) (hCSumInt.const_mul 2), integral_const_mul,
          integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hCInt i)]
  have hCost :
      (∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Wi i x‖^2) ≤
        2*(∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖V x‖^2)+
          (2*(cover.count : ℝ)*10000*M^8/betaFloor)*
            (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E F x) := by
    calc
      _ ≤ 2*(∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖V x‖^2)+
          2*∑ i : Fin cover.count, ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖Ccut i x‖^2 := hRawCost
      _ ≤ 2*(∫ x : R3, referenceDensityFamily S.g1 L (q,x)*‖V x‖^2)+
          2*(((cover.count : ℝ)*Q/betaFloor)*
            (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E F x)) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hCSum (by norm_num))
      _ = _ := by dsimp only [Q]; ring
  have hEInt (G : smoothCompactFiniteSphereCore hO hD) :
      Integrable (fun x : R3 => referenceDensityFamily S.g1 L (q,x)*E G x) :=
    integrable_finiteCoreReferenceProfileEnergy hO hD S.g1 S.g1_admissible L q beta
      hBetaContinuous hBetaPositive G
  have hPartitionPoint (x : R3) : E F x ≤ (cover.count : ℝ)*∑ i, E (Fi i) x :=
    finiteCoreReferenceProfileEnergy_partition_le hO hD S.g1 S.g1_admissible L q
      (beta x) (hBetaPositive x).le cover.count theta hTheta hPartition F
      (fun y hy => interior_subset (hFS hy)) x
  have hESumInt : Integrable (fun x : R3 =>
      ∑ i : Fin cover.count, referenceDensityFamily S.g1 L (q,x)*E (Fi i) x) :=
    integrable_finsetSum _ (fun i _ => hEInt (Fi i))
  have hPartitionInt :
      (∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E F x) ≤
        (cover.count : ℝ)*∑ i : Fin cover.count,
          ∫ x : R3, referenceDensityFamily S.g1 L (q,x)*E (Fi i) x := by
    calc
      _ ≤ ∫ x : R3, (cover.count : ℝ)*
          (∑ i : Fin cover.count, referenceDensityFamily S.g1 L (q,x)*E (Fi i) x) := by
        apply integral_mono (hEInt F) (hESumInt.const_mul (cover.count : ℝ))
        intro x
        exact (mul_le_mul_of_nonneg_left (hPartitionPoint x) (hDensityNonneg x)).trans_eq (by
          simp only [Finset.mul_sum]
          ring)
      _ = _ := by
        rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hEInt (Fi i))]
  refine ⟨?_, hWiInt, hCost, hPartitionPoint, hPartitionInt⟩
  intro i
  exact hWData i

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
