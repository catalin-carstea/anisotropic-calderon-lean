import Calderon.NativeSmoothSharpTraceCompletion
import Calderon.ActualReferenceTwoAngleStrongFullGreen
import Calderon.ActualReferenceTwoAngleAdjointH2FullGreen
import Calderon.NativeSupportedAdjointConormalPairing

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-H2-conormal-adjunction-v097.md. SAME actual H2 solutions. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData in
lemma referenceTwoAngleEnergy_adjoint_Green
    (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0 v u =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ)
      (fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      (fun x => -nativeSupportedDriftDivergence
        (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) x) u v +
      sphereSurfaceMass * ⟪sphereContinuousScalarMulL
        (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
          (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
          (SpatialJetFields.contDiff_spatial_slice _
            (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t)))
        (τ0.valueTraceL u),τ0.valueTraceL v⟫_ℝ := by
  let A : MatrixField := fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x)
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  have hA : Continuous A := (SpatialJetFields.contDiff_spatial_slice _
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t).continuous
  have hp : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_nativeEnergyIntegrand_of_continuous A 0 0 hA continuous_const continuous_const
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t
  have h := nativeSupportedEnergy_adjoint_Green τ0 A hp (0 : SmoothCoefficientJets 1) beta hbeta u v
  have hZero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  have hNeg : (-(fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) : R3 → R3) =
      (fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) := rfl
  simpa only [hZero,Pi.zero_apply,zero_sub,A,beta,hNeg] using h

attribute [local irreducible] referenceTwoAngleHarmonicLiftFamily
  referenceTwoAngleAdjointH2LiftFamily ordinaryConormalTraceL

lemma referenceTwoAngleH2Conormal_adjoint_pairing
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (E : BallSobolev 2) (z : SphereSobolev (3/2:ℝ)) :
    let U := referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E
    let V := referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t z
    ⟪ordinaryConormalTraceL hcalc τ0
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) U,
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)⟫_ℝ =
    ⟪ordinaryConormalTraceL hcalc τ0
        (nativePrincipalTransposeJets
          (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) V,
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ +
    ⟪sphereContinuousScalarMulL
        (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
          (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
          (SpatialJetFields.contDiff_spatial_slice _
            (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t)))
        (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 V)),
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ := by
  let U := referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E
  let V := referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t z
  let u1 : BallH1 := TauCeti.Wkp.firstOrder 1 U
  let v1 : BallH1 := TauCeti.Wkp.firstOrder 1 V
  let sigma : ℝ := sphereSurfaceMass
  let e0 : ℝ := TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0 u1 v1
  let eA : ℝ := TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ)
    (fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
    (fun x => -nativeSupportedDriftDivergence
      (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) x) v1 u1
  let p0 : ℝ := ⟪ordinaryConormalTraceL hcalc τ0
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) U,
    τ0.valueTraceL v1⟫_ℝ
  let pA : ℝ := ⟪ordinaryConormalTraceL hcalc τ0
    (nativePrincipalTransposeJets
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) V,
    τ0.valueTraceL u1⟫_ℝ
  let nb : ℝ := ⟪sphereContinuousScalarMulL
    (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t)))
    (τ0.valueTraceL v1),τ0.valueTraceL u1⟫_ℝ
  have hPrimal : sigma⁻¹ * e0 = p0 :=
    referenceTwoAngleHarmonicLiftFamily_normalized_full_test_energy_Green
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 i j k l t hStrong E v1
  have hAdjoint : eA = sigma * pA :=
    referenceTwoAngleAdjointH2LiftFamily_full_test_energy_Green
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg hF i j k l t hOriginal z u1
  have hGreen : e0 = eA + sigma * nb :=
    referenceTwoAngleEnergy_adjoint_Green
      g L y0 Φ B ε C ρ H a w hData τ0 i j k l t v1 u1
  have hSigma : 0 < sigma := NativeSmoothSharpTraceCompletion.sphereSurfaceMass_pos
  have hNormalized : sigma⁻¹ * e0 = sigma⁻¹ * eA + nb :=
    nativeNormalizedAdjointGreenPairing sigma e0 eA nb hSigma hGreen
  have hAdjNormalized : sigma⁻¹ * eA = pA := by
    have hScalar : sigma⁻¹ * eA = sigma⁻¹ * (sigma * pA) :=
      congrArg (fun x : ℝ => sigma⁻¹ * x) hAdjoint
    have hCancel : sigma⁻¹ * (sigma * pA) = pA := by
      rw [← mul_assoc,inv_mul_cancel₀ hSigma.ne',one_mul]
    exact hScalar.trans hCancel
  change p0 = pA + nb
  exact hPrimal.symm.trans (hNormalized.trans
    (congrArg (fun x : ℝ => x + nb) hAdjNormalized))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleEnergy_adjoint_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleH2Conormal_adjoint_pairing
