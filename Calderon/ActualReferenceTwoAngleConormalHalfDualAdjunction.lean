import Calderon.ActualReferenceTwoAngleH2ConormalAdjunction
import Calderon.ActualReferenceTwoAngleStrongBoundaryTrace
import Calderon.ActualReferenceTwoAngleAdjointSharpConormalFamily
import Calderon.ActualReferenceTwoAngleNormalHalfDualAdjunction
import Calderon.NativeHarmonicHalfCoarseDualPairing
import Calderon.NativeZeroValueTrace

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-conormal-half-duality-v101.md. Actual uncompressed H2 solutions. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativePolynomialBulkMoments
  NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeHalfCoefficientConormalTrace NativeHarmonicHalfCoarseDualPairing
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma sphereSobolevDualPairing_referenceTwoAngleAdjointHighConormal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (h : SphereSobolev (1/2:ℝ)) (z : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) h
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceTwoAngleAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 i j k l t z)) =
    ⟪ordinaryConormalTraceL hcalc τ0 (nativePrincipalTransposeJets
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t))
        (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t z),
      τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF h)⟫_ℝ := by
  let F := nativePrincipalTransposeJets
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
  let V := referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t z
  let b := referenceTwoAngleAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t z
  let I := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let K := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  have hBase : I b = Z (ordinaryConormalTraceL hcalc τ0 F V) :=
    sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F V
  have hTrans : J (I b)=K b := congrArg
    (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T b)
    (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  have hGraph : K b = J (Z (ordinaryConormalTraceL hcalc τ0 F V)) :=
    hTrans.symm.trans (congrArg J hBase)
  exact (congrArg (fun y : SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevDualPairing (1/2:ℝ) h y) hGraph).trans
      (sphereSobolevDualPairing_coarse_eq_halfLift_trace hF hO hD τ0 h
        (ordinaryConormalTraceL hcalc τ0 F V))

attribute [local irreducible] referenceTwoAngleHarmonicLiftFamily
  referenceTwoAngleAdjointH2LiftFamily ordinaryConormalTraceL

lemma sphereSobolevDualPairing_referenceTwoAngleH2Conormal_adjoint
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f z : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) z)
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD
        (ordinaryConormalTraceL hcalc τ0
          (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
          (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
            (harmonicLiftCompletion hF f))))) =
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceTwoAngleAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 i j k l t z)) +
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceTwoAngleNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
          i j k l hcalc hF hO hD τ0 t
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) z))) := by
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  let U := referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
    (harmonicLiftCompletion hF f)
  let V := referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t z
  let f0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let z0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) z
  let Ef := harmonicFirstOrderLiftCompletion hF f0
  let Ez := harmonicFirstOrderLiftCompletion hF z0
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t
  let CN := sphereContinuousScalarMulL (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
  have hDU : Ef-TauCeti.Wkp.firstOrder 1 U ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    referenceTwoAngleHarmonicLiftFamily_half_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l t hStrong f
  have hDV : Ez-TauCeti.Wkp.firstOrder 1 V ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    referenceTwoAngleAdjointH2LiftFamily_zero_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l t z
  have hTU : τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)=τ0.valueTraceL Ef := by
    have h0 := valueTraceL_eq_zero_of_mem_w1p0 τ0 _ hDU
    have hs : τ0.valueTraceL Ef-τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)=0 := by
      simpa only [map_sub] using h0
    exact (sub_eq_zero.mp hs).symm
  have hTV : τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)=τ0.valueTraceL Ez := by
    have h0 := valueTraceL_eq_zero_of_mem_w1p0 τ0 _ hDV
    have hs : τ0.valueTraceL Ez-τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)=0 := by
      simpa only [map_sub] using h0
    exact (sub_eq_zero.mp hs).symm
  have hPair := referenceTwoAngleH2Conormal_adjoint_pairing
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg hF i j k l t hOriginal hStrong
      (harmonicLiftCompletion hF f) z
  have hLeft := congrArg (fun v : SphereL2 => ⟪ordinaryConormalTraceL hcalc τ0 F U,v⟫_ℝ) hTV
  have hRight := congrArg (fun v : SphereL2 =>
    ⟪ordinaryConormalTraceL hcalc τ0 (nativePrincipalTransposeJets F) V,v⟫_ℝ) hTU
  have hNormal := congrArg₂ (fun u v : SphereL2 => ⟪CN u,v⟫_ℝ) hTV hTU
  have hBoundary : ⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL Ez⟫_ℝ =
      ⟪ordinaryConormalTraceL hcalc τ0 (nativePrincipalTransposeJets F) V,τ0.valueTraceL Ef⟫_ℝ +
        ⟪CN (τ0.valueTraceL Ez),τ0.valueTraceL Ef⟫_ℝ :=
    hLeft.symm.trans (hPair.trans (congrArg₂ (fun x y : ℝ => x+y) hRight hNormal))
  have hCoarse := sphereSobolevDualPairing_coarse_eq_halfLift_trace
    hF hO hD τ0 z0 (ordinaryConormalTraceL hcalc τ0 F U)
  have hAdj := sphereSobolevDualPairing_referenceTwoAngleAdjointHighConormal
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t f0 z
  have hDrift := sphereSobolevDualPairing_referenceTwoAngleNormalDriftHalfMultiplier
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t f0 z0
  exact hCoarse.trans (hBoundary.trans
    (congrArg₂ (fun x y : ℝ => x+y) hAdj.symm hDrift.symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleAdjointHighConormal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleH2Conormal_adjoint
