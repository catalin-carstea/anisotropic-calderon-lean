import Calderon.ActualMixedKernelNativeH3Datum
import Calderon.ActualReferencePhysicalCoefficientNativeIdentity
import Calderon.ActualReferencePhysicalOrientation

/-! Separate author draft; exact mathematical expansion was written first in
ActualMixedKernelDensityPacketCoherence_20261024_UPFRONT.md. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume NativeH3CoefficientConormalTrace
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint

attribute [local irreducible] nativeMixedKernelHighDensity referencePhysicalGaugeConormalDensity
  referencePhysicalGaugeCoefficientJets ordinaryPrincipalL nativePrincipalHarmonicConormalDensity
  nativeThreeHalfCoefficientConormalTraceL strongHarmonicProjectionL coefficientMultiplier

lemma coefficientMultiplier_eq_of_value_ae
    (hcalc : FixedSobolevCalculus) (k : ℕ) (F G : SmoothCoefficientJets (k+1))
    (hFG : coefficientValue (k+1) F =ᵐ[(volume : Measure R3).restrict ballOpens]
      coefficientValue (k+1) G) :
    coefficientMultiplier hcalc k F = coefficientMultiplier hcalc k G := by
  apply ContinuousLinearMap.ext
  intro U
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F U,
    coefficientMultiplier_value_ae hcalc k G U,hFG] with z hF hG hFG
  rw [hF,hG,hFG]

lemma packetEndpoint_eventuallyEq_on_overlap
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i j : Fin cover.count) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers ∩ (cover.packet j).centers)
    (r : ℝ) (hr : 0 < r) (hrc : r < cover.radiusCeiling)
    (z : R3) (hz : z ∈ ball (0 : R3) 2) :
    packetEndpoint S L (cover.packet i) q y r =ᶠ[𝓝 z]
      packetEndpoint S L (cover.packet j) q y r := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact cover.endpoint_coherence i j q hq y hy r hr hrc w (ball_subset_closedBall hw)

lemma principalCoefficient_packetPullback_eq_radius_gauge
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (k : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-P.y0‖ ≤ 4*P.rho)
    (r : ℝ) (hr : |r| ≤ 4*P.rho) (hrpos : 0 < r)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    principalCoefficient (pullbackMetric (fun x => S.g1 (q • x))
      (packetEndpoint S L P q y r)) z =
      r • coefficientMatrixField k (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L
        P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data k (q,(y,r))) z := by
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets]
  dsimp only
  rw [referencePhysicalGaugeCompactPrincipalCoefficient_eq_weighted_native
    S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data]
  exact principalCoefficient_referencePhysicalPullback_eq_pos_radius_smul_native
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w
    P.native_data q hq y hy r hr hrpos z hz

lemma coefficientMatrixField_packet_eq_on_overlap
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i j : Fin cover.count) (k : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers ∩ (cover.packet j).centers)
    (r : ℝ) (hr : 0 < r) (hrc : r < cover.radiusCeiling)
    (z : R3) (hz : z ∈ ball (0 : R3) 2) :
    coefficientMatrixField k (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L
      (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo
      (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a
      (cover.packet i).w (cover.packet i).native_data k (q,(y,r))) z =
    coefficientMatrixField k (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L
      (cover.packet j).y0 (cover.packet j).Phi (cover.packet j).B (cover.packet j).epsGeo
      (cover.packet j).Cgeo (cover.packet j).rho (cover.packet j).H (cover.packet j).a
      (cover.packet j).w (cover.packet j).native_data k (q,(y,r))) z := by
  have hq1 : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1,hq.2.trans cover.dilation_le_one⟩
  have hri : |r| ≤ 4*(cover.packet i).rho := by
    rw [abs_of_pos hr]
    exact (hrc.trans (cover.radius_room i)).le
  have hrj : |r| ≤ 4*(cover.packet j).rho := by
    rw [abs_of_pos hr]
    exact (hrc.trans (cover.radius_room j)).le
  have hGerm := packetEndpoint_eventuallyEq_on_overlap S L cover i j q hq y hy r hr hrc z hz
  have hMetric : pullbackMetric (fun x => S.g1 (q • x)) (packetEndpoint S L (cover.packet i) q y r) z =
      pullbackMetric (fun x => S.g1 (q • x)) (packetEndpoint S L (cover.packet j) q y r) z := by
    unfold pullbackMetric
    rw [hGerm.fderiv_eq,hGerm.eq_of_nhds]
  have hPrincipal := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => Real.sqrt M.det • M⁻¹) hMetric
  change principalCoefficient _ z = principalCoefficient _ z at hPrincipal
  have hi := principalCoefficient_packetPullback_eq_radius_gauge S L (cover.packet i) k q hq1 y
    ((cover.packet i).centers_room y hy.1).1.le r hri hr z (ball_subset_closedBall hz)
  have hj := principalCoefficient_packetPullback_eq_radius_gauge S L (cover.packet j) k q hq1 y
    ((cover.packet j).centers_room y hy.2).1.le r hrj hr z (ball_subset_closedBall hz)
  have hA := hi.symm.trans (hPrincipal.trans hj)
  have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => r⁻¹ • M) hA
  simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using hc

lemma nativeMixedKernelPullbackHkDatum_eq_on_overlap
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i j : Fin cover.count) (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) (k : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers ∩ (cover.packet j).centers)
    (r : ℝ) (hr : 0 < r) (hrc : r < cover.radiusCeiling) :
    nativeMixedKernelPullbackHkDatum S L (cover.packet i) Gext hG k (q,(y,r)) =
      nativeMixedKernelPullbackHkDatum S L (cover.packet j) Gext hG k (q,(y,r)) := by
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  unfold nativeMixedKernelPullbackHkDatum
  filter_upwards [value_smoothBallSobolev_ae k
      (nativeMixedKernelPullbackDatum S L (cover.packet i) Gext hG (q,(y,r))),
    value_smoothBallSobolev_ae k
      (nativeMixedKernelPullbackDatum S L (cover.packet j) Gext hG (q,(y,r))),
    ae_restrict_mem (show MeasurableSet (ballOpens : Set R3) from isOpen_ball.measurableSet)]
    with z hi hj hz
  rw [hi,hj]
  change Gext (packetEndpoint S L (cover.packet i) q y r z,y) =
    Gext (packetEndpoint S L (cover.packet j) q y r z,y)
  have hz2 : z ∈ closedBall (0 : R3) 2 := by
    have hz' : z ∈ ball (0 : R3) 1 := hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz' 
    simp only [mem_closedBall,dist_zero_right]
    linarith
  rw [cover.endpoint_coherence i j q hq y hy r hr hrc z hz2]

lemma coefficientValue_packet_eq_ae_on_overlap
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i j : Fin cover.count) (k : ℕ) (m n : Fin 3)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers ∩ (cover.packet j).centers)
    (r : ℝ) (hr : 0 < r) (hrc : r < cover.radiusCeiling) :
    coefficientValue k (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L
      (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo
      (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a
      (cover.packet i).w (cover.packet i).native_data k (q,(y,r)) m n) =ᵐ[(volume : Measure R3).restrict ballOpens]
    coefficientValue k (referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L
      (cover.packet j).y0 (cover.packet j).Phi (cover.packet j).B (cover.packet j).epsGeo
      (cover.packet j).Cgeo (cover.packet j).rho (cover.packet j).H (cover.packet j).a
      (cover.packet j).w (cover.packet j).native_data k (q,(y,r)) m n) := by
  filter_upwards [ae_restrict_mem
    (show MeasurableSet (ballOpens : Set R3) from isOpen_ball.measurableSet)] with z hz
  have hz2 : z ∈ ball (0 : R3) 2 := by
    have hz' : z ∈ ball (0 : R3) 1 := hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz' 
    simp only [mem_ball,dist_zero_right]
    linarith
  exact congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A m n)
    (coefficientMatrixField_packet_eq_on_overlap S L cover i j k q hq y hy r hr hrc z hz2)

lemma ordinaryPrincipalL_eq_of_coefficientValue_ae
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F G : SmoothCoefficientMatrix (s+2))
    (hFG : ∀ i j, coefficientValue (s+2) (F i j) =ᵐ[(volume : Measure R3).restrict ballOpens]
      coefficientValue (s+2) (G i j)) :
    ordinaryPrincipalL hcalc s F = ordinaryPrincipalL hcalc s G := by
  apply ContinuousLinearMap.ext
  intro U
  rw [ordinaryPrincipalL_apply,ordinaryPrincipalL_apply]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficientMultiplier_eq_of_value_ae hcalc (s+1) (F i j) (G i j) (hFG i j)]

lemma nativeThreeHalfCoefficientConormalTraceL_eq_of_coefficientValue_ae
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientMatrix 3)
    (hFG : ∀ i j, coefficientValue 3 (F i j) =ᵐ[(volume : Measure R3).restrict ballOpens]
      coefficientValue 3 (G i j)) :
    nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F =
      nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 G := by
  apply ContinuousLinearMap.ext
  intro U
  rw [nativeThreeHalfCoefficientConormalTraceL_apply,nativeThreeHalfCoefficientConormalTraceL_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficientMultiplier_eq_of_value_ae hcalc 2 (F i j) (G i j) (hFG i j)]


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
