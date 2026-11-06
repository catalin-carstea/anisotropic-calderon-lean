import Calderon.ActualReferencePhysicalCoefficientNativeIdentity
import Calderon.SmoothCommonSupportStrongOperator
import Calderon.SmoothPositiveCoefficientNativeCoercivity
import Calderon.NativePrincipalHarmonicConormalDensity

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic

/-- The actual exp(depth)-weighted native coefficient with its original spatial cutoff. -/
def referencePhysicalGaugeCompactPrincipalCoefficient
    (g : MatrixField) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (p : (ℝ × (R3 × ℝ)) × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  coefficientSpatialBump p.2 •
    (Real.exp (L*referenceRescaledDepth g L Φ p.1 p.2) • matrixPrincipalCoefficient H p)

theorem referencePhysicalGaugeCompactPrincipalCoefficient_eq_on_unitBall
    (g : MatrixField) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (p : ℝ × (R3 × ℝ)) (z : R3) (hz : ‖z‖ ≤ 1) :
    referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z) =
      Real.exp (L*referenceRescaledDepth g L Φ p z) • matrixPrincipalCoefficient H (p,z) := by
  rw [referencePhysicalGaugeCompactPrincipalCoefficient,coefficientSpatialBump_eq_one z hz,one_smul]

theorem referencePhysicalGaugeCompactPrincipalCoefficient_eq_zero_outside
    (g : MatrixField) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ closedBall (0 : R3) 3) :
    referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z) = 0 := by
  have hn : 3 ≤ ‖z‖ := le_of_lt (lt_of_not_ge (by
    simpa only [mem_closedBall,dist_zero_right] using hz))
  rw [referencePhysicalGaugeCompactPrincipalCoefficient,coefficientSpatialBump_eq_zero z hn,zero_smul]

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData in
theorem referencePhysicalGaugeCompactPrincipalCoefficient_eq_weighted_native
    (p : (ℝ × (R3 × ℝ)) × R3) :
    referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H p =
      Real.exp (L*referenceRescaledDepth g L Φ p.1 p.2) • a p := by
  rcases hData.1 with ⟨_,_,_,_,ha,_,_,_,_,_,_,_,_,_,_⟩
  rw [ha,cutoffPrincipalCoefficient,referencePhysicalGaugeCompactPrincipalCoefficient,smul_comm]

include hg hData in
theorem contDiff_referencePhysicalGaugeCompactPrincipalCoefficient :
    ContDiff ℝ ∞ (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H) :=
  (coefficientSpatialBump.contDiff.comp contDiff_snd).smul
    (contDiff_referencePhysicalGaugePrincipalCoefficient g hg L y0 Φ B ε C ρ H a w hData)

include hg hData in
theorem exists_compact_uniformlyElliptic_referencePhysicalGaugeCompactPrincipalCoefficient
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ∃ lam Lam : ℝ, ∀ p ∈ Q, TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1)
      (fun z => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z)) lam Lam := by
  let A : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ := fun v =>
    Real.exp (L*referenceRescaledDepth g L Φ v.1 v.2) • matrixPrincipalCoefficient H v
  have hA : ContDiff ℝ ∞ A :=
    contDiff_referencePhysicalGaugePrincipalCoefficient g hg L y0 Φ B ε C ρ H a w hData
  obtain ⟨lam,Lam,hUE⟩ := exists_compact_matrix_uniformlyElliptic A hA.continuous Q hQ
    (closedBall (0 : R3) 1) (isCompact_closedBall _ _) (fun v _ =>
      referencePhysicalGaugePrincipalCoefficient_posDef g L y0 Φ B ε C ρ H a w hData v.1 v.2)
  refine ⟨lam,Lam,fun p hp => (hUE p hp).congr ?_⟩
  intro z hz
  exact referencePhysicalGaugeCompactPrincipalCoefficient_eq_on_unitBall g L Φ H p z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)

def referencePhysicalGaugeCoefficientJets (k : ℕ) (p : ℝ × (R3 × ℝ)) :
    SmoothCoefficientMatrix k :=
  commonSupportMatrixFamily k (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H)
    (contDiff_referencePhysicalGaugeCompactPrincipalCoefficient g hg L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referencePhysicalGaugeCompactPrincipalCoefficient_eq_zero_outside g L Φ H) p

include hg hData in
theorem coefficientMatrixField_referencePhysicalGaugeCoefficientJets
    (k : ℕ) (p : ℝ × (R3 × ℝ)) :
    coefficientMatrixField k (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData k p) =
      fun z => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z) := by
  exact coefficientMatrixField_commonSupportMatrixFamily k _ _ _ _ _ p

include hg hData in
theorem coefficientValue_referencePhysicalGaugeCoefficientJets
    (k : ℕ) (p : ℝ × (R3 × ℝ)) (i j : Fin 3) :
    coefficientValue k (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData k p i j) =
      fun z => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z) i j := by
  funext z
  exact congrArg (fun A : MatrixField => A z i j)
    (coefficientMatrixField_referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData k p)

include hg hData in
theorem referencePhysicalGaugePrincipal_isInvertible
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (p : ℝ × (R3 × ℝ)) :
    (strongDirichletOperator hcalc s
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)).IsInvertible := by
  obtain ⟨lam,Lam,hUE⟩ :=
    exists_compact_uniformlyElliptic_referencePhysicalGaugeCompactPrincipalCoefficient
      g hg L y0 Φ B ε C ρ H a w hData {p} isCompact_singleton
  apply strongDirichletOperator_isInvertible_of_elliptic hcalc hreg s _
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets]
  exact (hUE p (by simp)).mono_set Metric.ball_subset_closedBall

include hg hData in
theorem referencePhysicalGauge_fullPrincipal_restriction_isInvertible
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (p : ℝ × (R3 × ℝ)) :
    ((ordinaryPrincipalL hcalc s
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)).comp
        (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible := by
  rw [ordinaryPrincipalL_restriction]
  exact referencePhysicalGaugePrincipal_isInvertible g hg L y0 Φ B ε C ρ H a w hData hcalc hreg s p

include hg hData in
theorem exists_compact_uniform_referencePhysicalGaugePrincipal_inverse_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ p ∈ Q, ∀ f : BallSobolev s,
      ‖(strongDirichletOperator hcalc s
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)).inverse f‖ ≤ C0*‖f‖ := by
  obtain ⟨lam,Lam,hUE⟩ :=
    exists_compact_uniformlyElliptic_referencePhysicalGaugeCompactPrincipalCoefficient
      g hg L y0 Φ B ε C ρ H a w hData Q hQ
  exact exists_uniform_commonSupportMatrixInverse_apply_bound hcalc hreg s _ _ _ _ _ Q hQ lam Lam
    (fun p hp => (hUE p hp).mono_set Metric.ball_subset_closedBall)


include hg hData in
theorem contDiff_referencePhysicalGauge_fullPrincipal
    (hcalc : FixedSobolevCalculus) (s : ℕ) :
    ContDiff ℝ ∞ (fun p => ordinaryPrincipalL hcalc s
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)) := by
  let A := referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H
  have hA := contDiff_referencePhysicalGaugeCompactPrincipalCoefficient g hg L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  have hK : IsCompact K := isCompact_closedBall _ _
  have hz : ∀ p z, z ∉ K → A (p,z) = 0 :=
    referencePhysicalGaugeCompactPrincipalCoefficient_eq_zero_outside g L Φ H
  have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc s
      (commonSupportMatrixFamily (s+2) A hA K hK hz p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc (s+1)
      (fun v => A v i j) (contDiff_pi.mp (contDiff_pi.mp hA i) j) K hK
      (fun p z h => by rw [hz p z h]; rfl)
  change ContDiff ℝ ∞ (fun p => coefficientDivergenceL
    (unitBallCoordinateDerivativeL hcalc s) (unitBallCoordinateDerivativeL hcalc (s+1))
      (coefficientMatrixMultiplierL hcalc s (commonSupportMatrixFamily (s+2) A hA K hK hz p)))
  exact (coefficientDivergenceL
    (unitBallCoordinateDerivativeL hcalc s) (unitBallCoordinateDerivativeL hcalc (s+1))).contDiff.comp hm

include hg hData in
theorem contDiff_referencePhysicalGauge_nativeThreeHalfConormal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun p => NativeH3CoefficientConormalTrace.nativeThreeHalfCoefficientConormalTraceL
      hcalc hF hO hD τ0
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p)) := by
  unfold NativeH3CoefficientConormalTrace.nativeThreeHalfCoefficientConormalTraceL
  refine ContDiff.sum fun i _ => ?_
  refine ContDiff.sum fun j _ => ?_
  have hm : ContDiff ℝ ∞ (fun p => coefficientMultiplier hcalc 2
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p i j)) := by
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 2
      (fun v => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H v i j)
      (contDiff_pi.mp (contDiff_pi.mp
        (contDiff_referencePhysicalGaugeCompactPrincipalCoefficient g hg L y0 Φ B ε C ρ H a w hData) i) j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun p z hz => by
        rw [referencePhysicalGaugeCompactPrincipalCoefficient_eq_zero_outside g L Φ H p z hz]
        rfl)
  exact contDiff_const.clm_comp (contDiff_const.clm_comp (hm.clm_comp contDiff_const))

def referencePhysicalGaugeConormalDensity
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (E : (ℝ × (R3 × ℝ)) → BallSobolev 3) (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2 : ℝ) :=
  nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 p.2.2
    (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p) (E p)

include hg hData in
theorem contDiffOn_referencePhysicalGaugeConormalDensity
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (E : (ℝ × (R3 × ℝ)) → BallSobolev 3) (Q : Set (ℝ × (R3 × ℝ)))
    (hE : ContDiffOn ℝ ∞ E Q) :
    ContDiffOn ℝ ∞ (referencePhysicalGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 E) Q := by
  let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3
  let A := fun p => ordinaryPrincipalL hcalc 1 (F p)
  have hA : ContDiff ℝ ∞ A :=
    contDiff_referencePhysicalGauge_fullPrincipal g hg L y0 Φ B ε C ρ H a w hData hcalc 1
  have hi : ∀ p ∈ Q, ((A p).comp (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible :=
    fun p _ => referencePhysicalGauge_fullPrincipal_restriction_isInvertible
      g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 1 p
  have hP := contDiffOn_strongHarmonicProjectionL 1 A Q hA.contDiffOn hi
  have hC := (contDiff_referencePhysicalGauge_nativeThreeHalfConormal
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn (s := Q)
  have hr : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => p.2.2) := contDiff_snd.snd
  exact (hr.contDiffOn.mul contDiffOn_const).smul
    (hC.clm_apply ((hP.clm_apply hE).sub hE))

include hg hData in
theorem referencePhysicalGaugeCoefficientJets_isSymm_on_unitBall
    (k : ℕ) (p : ℝ × (R3 × ℝ)) (z : R3) (hz : ‖z‖ ≤ 1) :
    (coefficientMatrixField k
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData k p) z).IsSymm := by
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets]
  change (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z)).IsSymm
  rw [referencePhysicalGaugeCompactPrincipalCoefficient_eq_on_unitBall g L Φ H p z hz]
  exact (referencePhysicalGaugePrincipalCoefficient_posDef g L y0 Φ B ε C ρ H a w hData p z).isHermitian.isSymm

attribute [local irreducible] referencePhysicalGaugeCoefficientJets ordinaryPrincipalL
  ordinaryConormalTraceL sphereSobolevInclusionL sphereSobolevZeroEquiv

include hg hData in
theorem referencePhysicalGaugeConormalDensity_represents_Wronskian
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (E : (ℝ × (R3 × ℝ)) → BallSobolev 3) (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2)
    (hU : ordinaryPrincipalL hcalc 0
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p) U = 0) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
        (referencePhysicalGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 E p)),
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ =
    p.2.2 * NativePolynomialBulkMoments.sphereSurfaceMass *
      (⟪τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 (E p)),ordinaryConormalTraceL hcalc τ0
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p) U⟫_ℝ -
      ⟪ordinaryConormalTraceL hcalc τ0
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)
        (TauCeti.Wkp.lowerOrder 2 (E p)),τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ) := by
  let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p
  let G := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p
  have hFG (i j : Fin 3) : coefficientValue 3 (F i j) = coefficientValue 2 (G i j) :=
    (coefficientValue_referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p i j).trans
      (coefficientValue_referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p i j).symm
  have hi := referencePhysicalGauge_fullPrincipal_restriction_isInvertible
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 1 p
  have hSym : ∀ᵐ z ∂(volume : Measure R3).restrict ballOpens, (coefficientMatrixField 2 G z).IsSymm := by
    filter_upwards [ae_restrict_mem (show MeasurableSet (ballOpens : Set R3) from isOpen_ball.measurableSet)] with z hz
    exact referencePhysicalGaugeCoefficientJets_isSymm_on_unitBall
      g hg L y0 Φ B ε C ρ H a w hData 2 p z
        (by
          have hz' : z ∈ Metric.ball (0 : R3) 1 := hz
          have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz'
          exact hn.le)
  exact nativePrincipalHarmonicConormalDensity_represents_Wronskian hcalc hF hO hD τ0 p.2.2
    F G hFG hi hSym (E p) U hU

end OAI.AnisotropicCalderon.ConnectionError
