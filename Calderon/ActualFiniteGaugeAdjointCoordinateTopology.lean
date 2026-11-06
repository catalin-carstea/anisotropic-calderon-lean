import Calderon.ActualFiniteGaugeAdjointCoordinateFamily
import Calderon.ActualFiniteGaugeAdjointValueGraphTopology

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
FINITE-GAUGE-ADJOINT-COORDINATE-MOVING-DOMAIN-EXPANSION-v001.md. Actual derivative AFTER coordinate product. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeFiniteHarmonicProductHighRotationL
  referenceFiniteGaugeAdjointRadialFamily sphereSobolevInclusionL
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL

variable {K0 : Set (ℝ × (R3 × ℝ))}

lemma contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_of_value_graph
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K0) (n : ℕ) (i : Fin 3)
    (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → m (p,x)=0)
    (Q : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3)
    (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => referenceFiniteGaugeAdjointCoordinateFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q z) z i) p := by
  let mj : Fin 3 → (ℝ × (R3 × ℝ)) × R3 → ℝ := fun j z => z.2 j * m z
  have hmj (j : Fin 3) : ContDiff ℝ ∞ (mj j) :=
    ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul hm
  have hzj (j : Fin 3) : ∀ z x, x ∉ K → mj j (z,x)=0 := by
    intro z x hx
    change x j * m (z,x)=0
    rw [hz z x hx,mul_zero]
  have hQj (j : Fin 3) : ∀ z,
      coefficientValue 3 (coefficientCoordinateJets (Q z) j) = fun x => mj j (z,x) := by
    intro z
    funext x
    exact (congrFun (coefficientValue_coordinateJets (Q z) j) x).trans
      (congrArg (fun t : ℝ => x j * t) (congrFun (hQ z) x))
  have hRotation : ContDiffAt ℝ ∞
      (fun z => ∑ j : Fin 3, nativeFiniteHarmonicProductHighRotationL
        hcalc hF hO hD τ0 n (coefficientCoordinateJets (Q z) j) j i) p := by
    apply ContDiffAt.sum
    intro j hj
    exact (contDiff_nativeFiniteHarmonicProductHighRotationL_of_value_graph
      hcalc hF hO hD τ0 n j i (mj j) (hmj j) K hK (hzj j)
        (fun z => coefficientCoordinateJets (Q z) j) (hQj j)).contDiffAt (x := p)
  have hRadial := contDiffAt_referenceFiniteGaugeAdjointRadialFamily_of_value_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (mj i) (hmj i) K hK (hzj i)
      (fun z => coefficientCoordinateJets (Q z) i) (hQj i) p hi
  unfold referenceFiniteGaugeAdjointCoordinateFamily
  exact hRotation.neg.add hRadial

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugeAdjointCoordinateFamily_of_value_graph
