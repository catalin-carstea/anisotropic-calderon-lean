import Calderon.ActualReferenceTwoAngleStrongWeakIdentification
import Calderon.ActualReferenceTwoAngleStrongFullGreen
import Calderon.ActualReferenceTwoAngleStrongBoundaryTrace
import Calderon.ActualReferenceTwoAngleWeakConormalCore
import Calderon.NativeHarmonicHalfCoarseDualPairing
import Calderon.NativeHalfTraceRightInverse

/-! SAME actual Green and trace graphs. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


open NativePolynomialBulkMoments NativeHarmonicHalfCoarseDualPairing
  NativeFullSharpHalfTrace NativeHalfTraceRightInverse

lemma referenceTwoAngleWeakConormalEndpointFamily_eq_conormal_of_original
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceTwoAngleWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD
      (ordinaryConormalTraceL hcalc τ0
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
        (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
          (harmonicLiftCompletion hF f)))) := by
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  have hco := firstOrder_referenceTwoAngleHarmonicLiftFamily_eq_nativeWeakHalfLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l t hOriginal hStrong f
  have he := sphereSobolevDualPairing_referenceTwoAngleWeakConormalEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) z
  have hn := referenceTwoAngleHarmonicLiftFamily_normalized_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 i j k l t hStrong
      (harmonicLiftCompletion hF f) (harmonicFirstOrderLiftCompletion hF z)
  have hEnergy := congrArg (fun U : BallH1 => sphereSurfaceMass⁻¹ *
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
        U (harmonicFirstOrderLiftCompletion hF z)) hco.symm
  exact (he.trans (hEnergy.trans hn)).trans
    (sphereSobolevDualPairing_coarse_eq_halfLift_trace hF hO hD τ0 z _).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakConormalEndpointFamily_eq_conormal_of_original
