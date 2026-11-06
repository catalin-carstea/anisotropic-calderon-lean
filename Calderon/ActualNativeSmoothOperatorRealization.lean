import Calderon.NativeSmoothOperatorRealization
import Calderon.ActualOrdinaryOperatorRadialJets
import Calderon.ActualRescaledConformalGauge
/-! Source-only author C5 actual specialization. Exact same-witness hData
and native calculus/room identities were fully expanded and sealed first.
No physical harmonic kernel premise, compiler, or Psi closure is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceOrdinaryStrongDriftFamily_smooth_value_ae
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (f : SmoothData) :
    TauCeti.Wkp.value s
      (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
        (smoothBallSobolev (s+2) f))
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) f.1 := by
  let hs := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  have hRaw := ordinaryStrongDriftFamily_smoothBallSobolev_value_ae hcalc s
    (jointFixedParameterSlice a q) hs.1
    (jointFixedParameterSlice w q) hs.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) hs.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) hs.2.2.2.1 hs.2.2.2.2 L (y,r) f
  change TauCeti.Wkp.value s
    (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
      (smoothBallSobolev (s+2) f))
    =ᵐ[_] fun x => (-∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun z => a ((q,(y,r)),z) i j * fderiv ℝ f.1 z (coordinateVector j)) x
        (coordinateVector i)) +
      inner ℝ (weightedDriftSlice (jointFixedParameterSlice w q)
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) L (y,r) x)
          (gradient f.1 x) at hRaw
  have hPositive := hData.1
  rcases hPositive with ⟨_,_,_,_,_,_,_,_,_,_,_,hLocal,_,_,_⟩
  have hPrincipal (z : R3) (hz : z ∈ (ballOpens : Set R3)) :
      a ((q,(y,r)),z) = principalCoefficient (fun x => H ((q,(y,r)),x)) z := by
    have hz2 : z ∈ closedBall (0 : R3) 2 := by
      change dist z (0 : R3) < 1 at hz
      change dist z (0 : R3) ≤ 2
      linarith
    have hL := hLocal q hq y hy r hr z hz2
    simpa only [principalCoefficient,vol,hL.1,matrixPrincipalCoefficient,matrixVolumeDensity]
      using hL.2.1
  have hA : ContDiff ℝ ∞ (fun z => a ((q,(y,r)),z)) :=
    hs.1.comp (contDiff_const.prodMk contDiff_id)
  have hTerm (x : R3) (i j : Fin 3) :
      DifferentiableAt ℝ
        (fun z => a ((q,(y,r)),z) i j * fderiv ℝ f.1 z (coordinateVector j)) x :=
    ((contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      (smoothCoordinateDerivative f j).2).differentiable (by simp) x
  have hDiv (x : R3) (hx : x ∈ (ballOpens : Set R3)) :
      coordinateFluxDivergence (metricDivergenceFlux (fun z => H ((q,(y,r)),z)) f.1) x =
        ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fun z => a ((q,(y,r)),z) i j * fderiv ℝ f.1 z (coordinateVector j)) x
            (coordinateVector i) := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    have hEq : (fun z => ∑ j : Fin 3,
        a ((q,(y,r)),z) i j * fderiv ℝ f.1 z (coordinateVector j)) =ᶠ[nhds x]
        (fun z => metricDivergenceFlux (fun v => H ((q,(y,r)),v)) f.1 z i) := by
      filter_upwards [ballOpens.isOpen.mem_nhds hx] with z hz
      rw [metricDivergenceFlux,matrixOperator_coordinate]
      simp_rw [gradient_coordinate]
      rw [← hPrincipal z hz]
    rw [← hEq.fderiv_eq]
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => a ((q,(y,r)),z) i j * fderiv ℝ f.1 z (coordinateVector j))
      (fun j _ => hTerm x i j)]
    simp only [sum_apply]
    rfl
  have hBeta (x : R3) :
      weightedDriftSlice (jointFixedParameterSlice w q)
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) L (y,r) x =
      conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),x) := by
    simp only [weightedDriftSlice,weightedLinearRadialDrift,jointFixedParameterSlice,
      conformalReferenceWeightedFramedDrift,parameterWeightedNormalizedConformalDrift,
      parameterNormalizedConformalDrift,normalizedConformalDrift,
      conformalReferenceFramedDriftBase,parameterNormalizedConformalDriftBase,smul_smul]
    congr 1
    ring
  apply hRaw.trans
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
  change (-∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun z => a ((q,(y,r)),z) i j * fderiv ℝ f.1 z (coordinateVector j)) x
        (coordinateVector i)) +
      inner ℝ (weightedDriftSlice (jointFixedParameterSlice w q)
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) L (y,r) x)
          (gradient f.1 x) =
    -coordinateFluxDivergence (metricDivergenceFlux (fun z => H ((q,(y,r)),z)) f.1) x +
      inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),x)) (gradient f.1 x)
  rw [hDiv x hx,hBeta]

theorem referenceOrdinaryStrongDriftFamily_smooth_eq_zero_iff
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (f : SmoothData) :
    referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
      (smoothBallSobolev (s+2) f) = 0 ↔
    referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) f.1
      =ᵐ[((volume : Measure R3).restrict ballOpens)] (0 : R3 → ℝ) := by
  have hValue := referenceOrdinaryStrongDriftFamily_smooth_value_ae
    g L y0 Φ B ε C ρ H a w hData hcalc s q hq y hy r hr f
  have hzero : TauCeti.Wkp.value s (0 : BallSobolev s) = 0 :=
    map_zero (TauCeti.Wkp.valueL s)
  constructor
  · intro h
    rw [h,hzero] at hValue
    exact hValue.symm.trans (Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens))
  · intro h
    apply TauCeti.Wkp.ext s
    rw [hzero]
    apply Lp.ext
    exact (hValue.trans h).trans
      (Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
