import Calderon.ActualNativePhysicalModelInputDictionary
import Calderon.ActualReferenceHighAdjointCoordinateZeroRaisingGraph
import Calderon.ActualNativeZeroCoordinateCovariantTransport

/-! Upfront: actual-physical-P-local-allocation-author-oct16-v001/
EXPANSION-model-T-dictionary-v004.md. Literal finite-input physical T, SAME model. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  NormalCoordinatesFrame ActualFiniteHarmonicCore ActualFiniteHarmonicModel AngularShiftGraph RadiusProfile ConformalDepth

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  referenceLowerAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus
  finiteCoreSobolevLift referenceHighHorizontalAction sphereSobolevInclusionL
  sphereSobolevAngularCoordinateTransposeL

include hData hg hcalc τ0

lemma referencePhysicalLeadingAction_finiteCore_eq_nativeT
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    (∑ i : Fin 3, sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
      (referenceHighHorizontalAction g L q (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) y i +
        referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i •
          sphereSobolevShiftedDegreeL (3/2 : ℝ)
            (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y))) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        ((nativeT hO hD hF g hg L q δ A p hδ hA F).val y)) := by
  let Z := sphereSobolevZeroEquiv hO hD
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let J0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let I0 := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let G := fun i : Fin 3 => coreReferenceInput hO hD g hg L q δ A p i hδ hA F
  let Ch := fun i : Fin 3 => referenceHighAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i
  have hp0 := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hp0Fields : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hp0
  unfold referenceRadialEndpointInvertibleLocus at hp0Fields
  have hInputDecode (i : Fin 3) :
      Z.symm (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)) = (G i).val y := by
    apply Z.injective
    simp only [LinearIsometryEquiv.apply_symm_apply]
    apply sphereSobolev_ext 0
    intro k
    rw [sphereSobolevCoefficientL_inclusion,
      sphereSobolevCoefficientL_finiteCoreSobolevLift,sphereSobolevCoefficientL_zeroEquiv]
  have hRaise (i : Fin 3) : J0 (Ch i (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)) =
      Z ((coreRaising hO hD hF i (G i)).val y) := by
    have hActual := referenceHighAdjointCoordinateBoundaryFamily_zero_raisingGraph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)
    have hGraph : ((G i).val y,
        Z.symm (J0 (Ch i (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)))) ∈
        sphereRaisingGraph hF hO hD i :=
      (congrArg (fun v : SphereL2 =>
        (v,Z.symm (J0 (Ch i (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)))) ∈
          sphereRaisingGraph hF hO hD i) (hInputDecode i)).mp hActual
    have hOut := sphereRaisingGraph_output_unique hF hO hD i _ _ _ hGraph
      (coreRaising_graph hO hD hF i (G i) y)
    have h := congrArg Z hOut
    simpa only [LinearIsometryEquiv.apply_symm_apply] using h
  have hTerm (i : Fin 3) :
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
        (referenceHighHorizontalAction g L q (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) y i +
          referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i •
            sphereSobolevShiftedDegreeL (3/2 : ℝ)
              (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y)) =
      I0 (Z ((coreRaising hO hD hF i (G i)).val y)) := by
    have hInputNative := referenceHighWeightedHorizontalAction_finiteCoreSobolevLift
      hO hD g hg L q δ A p hδ hA F y i
    have hLow := referenceLowerAdjointCoordinateBoundaryFamily_zero_eq_angularTranspose
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
    have hCoord := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        T (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y))
      (referenceAdjointCoordinateBoundaryFamily_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,0)) i hp0Fields.2.1)
    have hLowValue := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        T (Iin (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y))) hLow
    have hLift := sphereSobolevInclusionL_finiteCoreSobolevLift
      hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (G i) y
    have hA : sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
        (finiteCoreSobolevLift hO hD (1/2 : ℝ) (G i) y) =
        Iout (Ch i (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)) :=
      ((congrArg (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i)
        hLift).symm.trans hLowValue.symm).trans hCoord.symm
    have hTrans := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        T (Ch i (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)))
      (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
    have hInclusion : Iout (Ch i (finiteCoreSobolevLift hO hD (3/2 : ℝ) (G i) y)) =
        I0 (Z ((coreRaising hO hD hF i (G i)).val y)) :=
      hTrans.symm.trans (congrArg I0 (hRaise i))
    exact (congrArg (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i)
      hInputNative).trans (hA.trans hInclusion)
  have hModel : (nativeT hO hD hF g hg L q δ A p hδ hA F).val y =
      ∑ i : Fin 3, (coreRaising hO hD hF i (G i)).val y := by
    change nativeTField hO hD hF g hg L q δ A p F y = _
    rw [nativeTField_eq_coreAction hO hD hF g hg L q δ A p hδ hA F]
    simp only [coreReferenceRaisingAction,LinearMap.sum_apply,Module.End.mul_apply,
      Submodule.coe_sum,Finset.sum_apply,G]
  have hSum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i hi => hTerm i)
  have hModelIncluded := congrArg (fun v : SphereL2 => I0 (Z v)) hModel
  simp only [map_sum] at hModelIncluded
  exact hSum.trans hModelIncluded.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalLeadingAction_finiteCore_eq_nativeT
