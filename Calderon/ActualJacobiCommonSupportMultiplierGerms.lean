import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily
import Calderon.NativeBoundaryMultiplierLocalSmoothness
import Calderon.CommonSupportSphereFamilyExtension
import Calderon.NativeH2SmoothMultiplierDerivative

set_option autoImplicit false
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem exists_referenceJacobi_commonSupport_boundary_multiplier_germs
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (Kt : Set (ℝ × (R3 × ℝ))) (hKt : IsCompact Kt)
    (hInv : ∀ p ∈ Kt, ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    ∃ (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
      (Km : Set R3) (hKm : IsCompact Km)
      (hmz : ∀ p x, x ∉ Km → m (p,x)=0),
      ∀ p ∈ Kt, ∀ᶠ z in 𝓝 p,
        let Q := commonSupportCoefficientFamily 3 m hm Km hKm hmz z
        nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q =
          nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
            (referenceJacobiBoundaryThreeHalfCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData i j z) ∧
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) =
          nativeHalfCoefficientMulL hcalc hF hO hD τ0
            (referenceJacobiBoundaryCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData i j z) ∧
        nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) =
          nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
            (referenceJacobiBoundaryCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData i j z) := by
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let T : (ℝ × (R3 × ℝ)) × R3 → ReferenceEndpointVariables :=
    fun t => (t.1.1,(t.1.2,t.2))
  have hT : ContDiff ℝ ∞ T :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  let J : (ℝ × (R3 × ℝ)) × R3 → R3 →L[ℝ] R3 :=
    fun t => referenceFramedNormalizedJacobian g L Φ (T t)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hTheta).comp hT
  let S : Set ((ℝ × (R3 × ℝ)) × R3) := {t | (J t).IsInvertible}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact hJ.continuous.continuousAt.eventually ht.eventually_nhds
  let f : (ℝ × (R3 × ℝ)) × R3 → ℝ :=
    fun t => referenceFramedJacobiVelocityRemainder g L Φ i (T t) j
  have hf : ContDiffOn ℝ ∞ f S := by
    intro t ht
    exact (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.contDiffAt).comp t
      ((contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hTheta i (T t) ht).comp t
        hT.contDiffAt)).contDiffWithinAt
  obtain ⟨m,hm,Km,hKm,hmz,hNear⟩ :=
    exists_contDiff_commonSupport_eq_near_compact_sphere Kt hKt S hS f hf hInv
  refine ⟨m,hm,Km,hKm,hmz,?_⟩
  intro p hp
  filter_upwards [hNear p hp] with z hz
  intro Q
  have hIz : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,x.val))).IsInvertible :=
    fun x => (hz x).2
  have hSphere2 : smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q)) =
      smoothSphereValue (coefficientSmoothData
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)) := by
    apply ContinuousMap.ext
    intro x
    have hQ : coefficientValue 3 Q x.val = m (z,x.val) :=
      coefficientValue_commonSupportCoefficientFamily 3 m hm Km hKm hmz z x.val
    have hOriginal : smoothSphereValue (coefficientSmoothData
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)) x = f (z,x.val) := by
      rw [referenceJacobiBoundaryCoefficientFamily_eq
        g hg L y0 Φ B ε C ρ H a w hData i j z hIz,
        smoothSphereValue_referenceJacobiBoundaryCoefficientJets]
      rfl
    change coefficientValue 2 (smoothMultiplierLowerJets Q) x.val = _
    rw [coefficientValue_smoothMultiplierLowerJets]
    exact hQ.trans ((hz x).1.trans hOriginal.symm)
  have hSphere3 : smoothSphereValue (nativeH2CoefficientSmoothData Q) =
      smoothSphereValue (nativeH2CoefficientSmoothData
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)) := by
    apply ContinuousMap.ext
    intro x
    have hLower := congrArg (fun F : C(UnitSphere,ℝ) => F x) hSphere2
    change coefficientValue 2 (smoothMultiplierLowerJets Q) x.val =
      coefficientValue 2 (referenceJacobiBoundaryCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData i j z) x.val at hLower
    rw [coefficientValue_smoothMultiplierLowerJets] at hLower
    change coefficientValue 3 Q x.val =
      coefficientValue 3 (referenceJacobiBoundaryThreeHalfCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData i j z) x.val
    rw [referenceJacobiBoundaryThreeHalfCoefficientFamily,coefficientValue_compactCoefficient]
    exact hLower
  exact ⟨nativeThreeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0 _ _ hSphere3,
    nativeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0 _ _ hSphere2,
    nativeNegativeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0 _ _ hSphere2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobi_commonSupport_boundary_multiplier_germs
