import Calderon.ActualHalfGaugeCollarCoherence
import Calderon.NativeH2CoefficientFluxGreen
import Calderon.NativeHighDensityTracePairingDictionary
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap NativePolynomialBulkMoments SphereHarmonic
open NativeH2ThreeHalfValueTrace


private theorem nativeThreeHalfValueTrace_zero_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (V : BallSobolev 2) :
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 V) =
      sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_nativeThreeHalfValueTraceL,
    sphereSobolevCoefficientL_zeroEquiv]


private theorem nativeThreeHalfValueTrace_dualPairing_valueTrace
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (Psi : SphereSobolev (3/2 : ℝ)) (V : BallSobolev 2) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) Psi))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 V)) =
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Psi),
        τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)⟫_ℝ := by
  have hCompose (z : SphereSobolev (3/2 : ℝ)) :
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) z) =
      sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) z := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 => T z)
        (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) 0 (by norm_num) (by norm_num))
  let T : SphereSobolev (3/2 : ℝ) := nativeThreeHalfValueTraceL hcalc hF hO hD τ0 V
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hPair := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) (I Psi) (I T)
  have hBoth := congrArg₂ (fun x y : SphereSobolev 0 => inner ℝ x y) (hCompose Psi) (hCompose T)
  have hTrace := congrArg (fun x : SphereSobolev 0 =>
      inner ℝ (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Psi) x)
    (nativeThreeHalfValueTrace_zero_inclusion hcalc hF hO hD τ0 V)
  have h := ((sphereSobolevZeroEquiv hO hD).symm.inner_map_map
    (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Psi)
    (sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)))).symm
  have hIso := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h
  exact hPair.trans (hBoth.trans (hTrace.trans hIso))


private theorem nativePrincipal_zeroDirichlet_harmonic_energy
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (hSym : ∀ᵐ z ∂(volume : Measure R3).restrict ballOpens, (coefficientMatrixField 2 F z).IsSymm)
    (U : StrongDirichletSpace 0) (V : BallSobolev 2)
    (hV : ordinaryPrincipalL hcalc 0 F V = 0) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 (U : BallSobolev 2))
        (TauCeti.Wkp.firstOrder 1 V) = 0 := by
  let u0 : BallH1Zero := ⟨TauCeti.Wkp.firstOrder 1 (U : BallSobolev 2),U.property⟩
  have hEnergy := ordinaryPrincipalL_energy hcalc 0 F V u0
  have hForce : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F V)) u0 = 0 := by
    rw [hV]
    simp only [TauCeti.Wkp.value_zero,TauCeti.PDE.dirichletForcing_apply,_root_.inner_zero_left]
  have hZero : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 V)
        (TauCeti.Wkp.firstOrder 1 (U : BallSobolev 2)) = 0 := hEnergy.symm.trans hForce
  exact (TauCeti.PDE.energyFormH1_comm_of_isSymm_ae (c := (0 : R3 → ℝ)) hSym
    (TauCeti.Wkp.firstOrder 1 (U : BallSobolev 2)) (TauCeti.Wkp.firstOrder 1 V)).trans hZero


attribute [local irreducible] referencePhysicalHalfGaugeConormalDensity referencePhysicalHalfGaugeCollarCorrection
  referencePhysicalHalfGaugeCollarForcing referencePhysicalGaugeCoefficientJets ordinaryPrincipalL
  ordinaryConormalTraceL sphereSobolevInclusionL sphereSobolevZeroEquiv nativeThreeHalfValueTraceL

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0)
    (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η)


include hg hData hcalc in
theorem referencePhysicalHalfGaugeConormalDensity_harmonic_valueTrace_pairing
    (hreg : FixedDirichletRegularity) (a0 : ℝ)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) a0, ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) a0, η z = 0)
    (hηSphere : ∀ x : UnitSphere, η x.val = 1)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (V : BallSobolev 2)
    (hV : ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) V = 0) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r)))),
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)⟫_ℝ =
      -⟪(referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))),TauCeti.Wkp.value 2 V⟫_ℝ := by
  let G : SmoothCoefficientMatrix 2 := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))
  let U : StrongDirichletSpace 0 := referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))
  let f : BallSobolev 0 := referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))
  have hSym : ∀ᵐ z ∂(volume : Measure R3).restrict ballOpens, (coefficientMatrixField 2 G z).IsSymm := by
    filter_upwards [ae_restrict_mem (show MeasurableSet (ballOpens : Set R3) from isOpen_ball.measurableSet)] with z hz
    exact referencePhysicalGaugeCoefficientJets_isSymm_on_unitBall g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)) z
      (by
        have hz' : z ∈ ball (0 : R3) 1 := hz
        exact (show ‖z‖ < 1 from (by simpa only [mem_ball,dist_zero_right] using hz')).le)
  have hEnergy := nativePrincipal_zeroDirichlet_harmonic_energy hcalc G hSym U V hV
  have hU : ordinaryPrincipalL hcalc 0 G (U : BallSobolev 2) = f :=
    referencePhysicalHalfGaugeCollarCorrection_equation g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero hreg (q,(y,r))
  have hGreen := ordinaryPrincipalL_full_test_energy_Green hcalc τ0 G (U : BallSobolev 2)
    (TauCeti.Wkp.firstOrder 1 V)
  rw [hEnergy,hU] at hGreen
  simp only [TauCeti.Wkp.value_zero,TauCeti.Wkp.value_firstOrder] at hGreen
  have hPi := sphereSobolevInclusionL_zero_referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη
    hreg a0 hθOne hζOne hηZero hηSphere hF hO hD τ0 q hq y hy r hr
  have hPiL2 : (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r)))) =
      sphereSurfaceMass • ordinaryConormalTraceL hcalc τ0 G (U : BallSobolev 2) := by
    rw [hPi,map_smul,LinearIsometryEquiv.symm_apply_apply]
  rw [hPiL2,real_inner_smul_left]
  change sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 G (U : BallSobolev 2),
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)⟫_ℝ = -⟪f,TauCeti.Wkp.value 2 V⟫_ℝ
  linarith only [hGreen]


include hg hData hcalc in
theorem referencePhysicalHalfGaugeConormalDensity_harmonic_nativeTrace_pairing
    (hreg : FixedDirichletRegularity) (a0 : ℝ)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) a0, ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) a0, η z = 0)
    (hηSphere : ∀ x : UnitSphere, η x.val = 1)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (V : BallSobolev 2)
    (hV : ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) V = 0) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r)))))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 V)) =
      -⟪(referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))),TauCeti.Wkp.value 2 V⟫_ℝ := by
  exact (nativeThreeHalfValueTrace_dualPairing_valueTrace hcalc hF hO hD τ0
    (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r))) V).trans
    (referencePhysicalHalfGaugeConormalDensity_harmonic_valueTrace_pairing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη
      hreg a0 hθOne hζOne hηZero hηSphere hF hO hD τ0 q hq y hy r hr V hV)

end OAI.AnisotropicCalderon.ConnectionError
