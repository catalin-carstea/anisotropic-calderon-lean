import Calderon.ActualConstantOnePhysicalHalfRepresentative
import Calderon.ActualConstantOneHalfDecomposition
import Calderon.ConstantForcingHalfNormBound
import Calderon.ActualConstantForcingCoefficientCaps
import Calderon.ActualConstantModePrincipalHalfForcing
import Calderon.ActualUniformHighMovingDifferenceQuotient
import Calderon.ActualUniformRadiusScaledFirstAction
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth CoordinateBootstrapJets NormalizedPrincipalMetric ActualNormalizedSecondMetricDrift ReferenceDensityBounds
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceFiveHalfConstantFirstRegularPartInRoom
  referencePhysicalDensityHalfFromFirstSections referenceConstantOnePhysicalDensityHalfInRoom
  referenceConstantOneFirstSectionInRoom referenceHighDensityFirstAction sphereSobolevInclusionL
  referenceNativeMovingAdjointParametricCorrection constantOneFirstRaisingThreeHalf constantOneDoubleRaisingHalf
  referenceDensityPrincipalFrameCoefficient referenceFrameConnectionCoefficient referenceMetricGramFrame
  normalizedSecondDriftFrameJoint referenceHighAdjointMovingDifferenceQuotient constantOnePrincipalDifferenceHalf

theorem exists_uniform_referenceConstantOnePhysicalDensityHalfInRoom_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ q ∈ Icc (0:ℝ) 1, ∀ delta : ℝ, 0 < delta → ∀ Rstar : ℝ, 0 < Rstar →
      ∀ (p : ℕ) (eps : ℝ), 0 ≤ eps → eps ≤ 1 → ∀ y : R3, ‖y-y0‖ ≤ ρ →
      let R := referenceRadius delta Rstar p L
      |R y| ≤ d → ‖fderiv ℝ R y‖ ≤ 1 → ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ 1 →
      (∀ x : UnitSphere, (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) →
      coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) y ≤ eps*R y →
      ‖referenceConstantOnePhysicalDensityHalfInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 g2 q R y‖ ≤ C0 := by
  obtain ⟨dK,hdK,hdKρ,hdK1,MK,hMK,hKBounds⟩ :=
    exists_uniform_referenceFiveHalfConstantFirstRegularPartInRoom_radius_first_jets
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg
  obtain ⟨dJ,hdJ,hdJρ,hdJ1,MJ,hMJ,hJoint⟩ :=
    exists_uniform_referenceFiveHalfConstantFirstRegularPartInRoom_joint_first_jets
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg
  obtain ⟨dQ,hdQ,hdQρ,hdQ1,MQ,hMQ,hDQBounds⟩ :=
    exists_uniform_referenceHighAdjointMovingDifferenceQuotient_operator_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨MX,hMX,hXBounds⟩ := exists_uniform_radiusScaled_referenceHighDensityFirstAction_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg MK
  obtain ⟨MC,hMC,hIC,hAC,hCoeff⟩ := exists_compact_constantForcing_actual_coefficient_caps
    hF hO hD g g2 hg hg2 L (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨MS,hMS,hSingular⟩ := exists_uniform_constantOnePrincipalDifferenceHalf_bound
    hF g g2 hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  let d := min dK (min dJ dQ)
  let M := MK+MJ+MQ+MX+MC+MS
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hKM : MK ≤ M := by dsimp [M]; linarith
  have hQM : MQ ≤ M := by dsimp [M]; linarith
  have hXM : MX ≤ M := by dsimp [M]; linarith
  have hCM : MC ≤ M := by dsimp [M]; linarith
  have hSM : MS ≤ M := by dsimp [M]; linarith
  have hddK : d ≤ dK := min_le_left _ _
  have hddJ : d ≤ dJ := (min_le_right _ _).trans (min_le_left _ _)
  have hddQ : d ≤ dQ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨d,lt_min hdK (lt_min hdJ hdQ),hddK.trans hdKρ,hddK.trans hdK1,
    M+27*(2*M^2+M+3*M^3)+6*M^3,?_,?_⟩
  · have hM0 : 0 ≤ M := zero_le_one.trans hM
    have hRest : 0 ≤ 27*(2*M^2+M+3*M^3)+6*M^3 := by positivity
    linarith
  intro q hq delta hdelta Rstar hRstar p eps heps heps1 y hy R hrBound hDR hD2R hInv hBootstrap
  have hR : ContDiff ℝ ∞ R := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual
    delta Rstar p L hdelta hRstar
  have hr : R y ≠ 0 := (referenceRadius_pos delta Rstar p L y hdelta hRstar).ne'
  have hyK : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  let kappa : Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun j z =>
    referenceFiveHalfConstantFirstRegularPartInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(z,R z)),fderiv ℝ R z) j
  have hKcap (j : Fin 3) : ‖kappa j y‖ ≤ MK ∧ ‖fderiv ℝ (kappa j) y‖ ≤ MK :=
    hKBounds q hq R hR y hy (hrBound.trans hddK) hDR hD2R j
  have hGraph : ContDiffAt ℝ ∞ (fun z : R3 => ((q,(z,R z)),fderiv ℝ R z)) y :=
    (contDiffAt_const.prodMk (contDiffAt_id.prodMk hR.contDiffAt)).prodMk
      (hR.fderiv_right (m := ∞) (by simp)).contDiffAt
  have hKsmooth (j : Fin 3) : ContDiffAt ℝ ∞ (kappa j) y := by
    have h := (hJoint q hq y hy (R y) (hrBound.trans hddJ) (fderiv ℝ R y) hDR j).1
    simpa only [Function.comp_def] using h.comp y hGraph
  have hρ : 0 < ρ := hdK.trans_le hdKρ
  have hy4 : ‖y-y0‖ ≤ 4*ρ := hy.trans (by linarith)
  have hr1 : |R y| ≤ 1 := hrBound.trans (hddK.trans hdK1)
  have hr4 : |R y| ≤ 4*ρ := hrBound.trans ((hddK.trans hdKρ).trans (by linarith))
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Corr := fun i : Fin 3 => I.comp (referenceNativeMovingAdjointParametricCorrection
    hF hO hD g L (3/2:ℝ) ((q,y),fderiv ℝ R y) i)
  let DQ := fun i : Fin 3 => referenceHighAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let X := fun i j : Fin 3 => R y • referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (kappa j) y i
  let s := constantOnePrincipalDifferenceHalf hF g g2 L q delta Rstar p y
  have hs : ‖s‖ ≤ M := (hSingular q hq delta hdelta Rstar hRstar p eps heps y hyK hBootstrap).trans
    ((mul_le_of_le_one_right (zero_le_one.trans hMS) heps1).trans hSM)
  have hCorr (i : Fin 3) : ‖Corr i‖ ≤ M :=
    ((hCoeff q hq y hyK (fderiv ℝ R y) hDR i 0 0).1).trans hCM
  have hDQ (i : Fin 3) : ‖DQ i‖ ≤ M :=
    (hDQBounds q hq y hy R hR (hrBound.trans hddQ) hr hDR hInv i).trans hQM
  have hX (i j : Fin 3) : ‖X i j‖ ≤ M :=
    (hXBounds q hq R (kappa j) y hy4 (hR.differentiable (by simp) y) hr hr4 hDR
      (hKcap j).1 (hKcap j).2 i).trans hXM
  have hQ (i j : Fin 3) : |Q i j| ≤ 3 :=
    (hCoeff q hq y hyK (fderiv ℝ R y) hDR i j 0).2.2.2
  have hGamma (i j k : Fin 3) : |Gamma i j k| ≤ M :=
    ((hCoeff q hq y hyK (fderiv ℝ R y) hDR i j k).2.1).trans hCM
  have hb (i : Fin 3) : |b i| ≤ M :=
    ((hCoeff q hq y hyK (fderiv ℝ R y) hDR i 0 0).2.2.1).trans hCM
  have hNorm := ConstantForcingHalfNorm.norm_complete_constant_forcing_sum_le
    I Corr DQ (constantOneFirstRaisingThreeHalf hF) (fun j => kappa j y) X Q Gamma b s (R y) M
    hM hr1 hs (hIC.trans hCM) hCorr hDQ (fun i => (hAC i).trans hCM)
    (fun j => (hKcap j).1.trans hKM) hX hQ hGamma hb
  have hIdentity := referencePhysicalDensityHalfFromFirstSections_constant_leading_decomposition
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q hq R hR y hy hr kappa hKsmooth
  have hSingularIdentity : s = (R y)⁻¹ •
      (∑ i : Fin 3, ∑ j : Fin 3, (Q i j-(if i=j then (1:ℝ) else 0)) • constantOneDoubleRaisingHalf hF i j) := by
    dsimp only [s]
    delta constantOnePrincipalDifferenceHalf
    exact ConstantForcingHalfNorm.sum_div_smul_eq_inverse_smul_sum (R y)
      (fun i j : Fin 3 => Q i j-(if i=j then (1:ℝ) else 0)) (constantOneDoubleRaisingHalf hF)
  have hWithS := hIdentity.trans (congrArg (fun singular : SphereSobolev (1/2:ℝ) =>
    singular+(∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (Corr i (constantOneFirstRaisingThreeHalf hF j)+R y • DQ i (constantOneFirstRaisingThreeHalf hF j)+X i j-
        R y • (∑ k : Fin 3, Gamma i j k • I (kappa k y))))+
      (∑ i : Fin 3, b i • (I (constantOneFirstRaisingThreeHalf hF i)+R y • I (kappa i y))))
    hSingularIdentity.symm)
  delta referenceConstantOnePhysicalDensityHalfInRoom referenceConstantOneFirstSectionInRoom
  exact (congrArg (fun z : SphereSobolev (1/2:ℝ) => ‖z‖) hWithS).trans_le hNorm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
