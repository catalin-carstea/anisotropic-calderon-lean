import Calderon.ActualReferenceInvertibleStrongWeakCoherence
import Calderon.ActualReferenceWeakConormalEndpoint
import Calderon.NativeHarmonicHalfCoarseDualPairing

/-! Upfront expansion: EXPANSION-actual-reference-invertible-conormal-compatibility-v001.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SpectralCoreRegularity NativePolynomialBulkMoments
  NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open NativeHarmonicHalfCoarseDualPairing NativeSmoothSharpTraceCompletion

lemma referenceHarmonicLiftFamily_normalized_full_test_energy_Green
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (E : BallSobolev 2) (v : BallH1) :
    sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a ((q,p),x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),x)) 0
      (TauCeti.Wkp.firstOrder 1
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E)) v =
    ⟪referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E),
      τ0.valueTraceL v⟫_ℝ := by
  have hGreen := referenceHarmonicLiftFamily_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p hi E v
  have hnormalized := congrArg (fun t : ℝ => sphereSurfaceMass⁻¹ * t) hGreen
  rw [← mul_assoc,inv_mul_cancel₀ sphereSurfaceMass_pos.ne',one_mul] at hnormalized
  exact hnormalized

lemma sphereSobolevDualPairing_referenceWeakConormalEndpoint_of_isInvertible
    (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
      ⟪referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
          (harmonicLiftCompletion hF f)),τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)⟫_ℝ := by
  let Q : BallH1 → ℝ := fun u => sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => a ((q,p),x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),x)) 0
    u (harmonicFirstOrderLiftCompletion hF z)
  have hco := firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 q p hStrong hWeak f
  have he := referenceWeakConormalEndpointFamily_energy
    g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) z
  have hc : Q (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
      Q (TauCeti.Wkp.firstOrder 1
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
          (harmonicLiftCompletion hF f))) := congrArg Q hco.symm
  have hn := referenceHarmonicLiftFamily_normalized_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p hStrong
    (harmonicLiftCompletion hF f) (harmonicFirstOrderLiftCompletion hF z)
  exact (he.trans hc).trans hn

lemma referenceWeakConormalEndpointFamily_eq_conormal_of_isInvertible
    (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
          (sphereSobolevZeroEquiv hO hD
            (referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p
              (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
                (harmonicLiftCompletion hF f)))) := by
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  rw [sphereSobolevDualPairing_referenceWeakConormalEndpoint_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q p hStrong hWeak f z]
  exact (sphereSobolevDualPairing_coarse_eq_halfLift_trace hF hO hD τ0 z _).symm

lemma sphereSobolevCoefficientL_referenceWeakConormalEndpoint_of_isInvertible
    (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (k : ℕ) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) k
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
      sphereHarmonicCoordinate hO hD k
        (referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p
          (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
            (harmonicLiftCompletion hF f))) := by
  rw [referenceWeakConormalEndpointFamily_eq_conormal_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q p hStrong hWeak f,
    sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceWeakConormalEndpoint_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFamily_eq_conormal_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevCoefficientL_referenceWeakConormalEndpoint_of_isInvertible
