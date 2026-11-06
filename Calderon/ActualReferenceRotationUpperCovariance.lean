import Calderon.ActualReferenceRotationStrongIdentification
import Calderon.ActualReferenceOrthogonalSharpUpperEndpoint
import Calderon.ActualReferenceRadialEndpointOpenLocus

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation NativeFullHalfRadialTrace NativeHarmonicLiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
lemma eventually_snd_mem_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set Y) (hS : IsOpen S) (x : X) (y : Y) (hy : y ∈ S) :
    ∀ᶠ t : X × Y in 𝓝 (x,y), t.2 ∈ S :=
  continuous_snd.continuousAt.eventually (hS.mem_nhds hy)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceRotationSharpRadialTraceFamily_eq_orthogonal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (hRot : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).IsInvertible) :
    referenceRotationSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p) =
    referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p := by
  apply ContinuousLinearMap.ext
  intro f
  have he := congrArg (nativeHalfOutwardTraceL hF hO hD hcalc τ0)
    (referenceRotationHarmonicLiftFamily_eq_orthogonalStrongLift
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 i j θ p hStrong hWeak hRot f)
  exact he.trans (referenceOrthogonalSharpRadialTraceFamily_eq_actual_outward_trace
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p f).symm

lemma referenceRotationSharpRadialTraceFamily_coordinate_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (hRot : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceRotationSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry i j θ) f) =
    sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ)
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) := by
  rw [referenceRotationSharpRadialTraceFamily_eq_orthogonal
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hStrong hWeak hRot]
  exact referenceOrthogonalSharpRadialTraceFamily_orthogonal_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p f

attribute [local irreducible] referenceStrongDriftFamily referenceWeakDirichletEnergyFamily

lemma eventually_referenceStrongDriftFamily_zero_isInvertible_product
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ∀ᶠ t : ℝ × (ℝ × (R3 × ℝ)) in 𝓝 (0,p),
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 t.2.1 t.2.2).IsInvertible := by
  exact eventually_snd_mem_of_isOpen
    {q : ℝ × (R3 × ℝ) | (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q.1 q.2).IsInvertible}
    (isOpen_referenceStrongDriftFamily_zero_invertible_set g L y0 Φ B ε C ρ H a w hData hcalc)
    (0 : ℝ) p hStrong

lemma eventually_referenceWeakDirichletEnergyFamily_isInvertible_product
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ∀ᶠ t : ℝ × (ℝ × (R3 × ℝ)) in 𝓝 (0,p),
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible := by
  exact eventually_snd_mem_of_isOpen
    {q : ℝ × (R3 × ℝ) | (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc q).IsInvertible}
    (isOpen_referenceWeakDirichletEnergyFamily_invertible_set g L y0 Φ B ε C ρ H a w hData hcalc)
    (0 : ℝ) p hWeak

lemma contDiffAt_referenceOrthogonalSharpRadialTraceFamily_joint_zero_angle
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) =>
      referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (coordinateRotationIsometry i j t.1) t.2) (0,p) := by
  have hS := eventually_referenceStrongDriftFamily_zero_isInvertible_product
    g L y0 Φ B ε C ρ H a w hData hcalc p hStrong
  have hW := eventually_referenceWeakDirichletEnergyFamily_isInvertible_product
    g L y0 Φ B ε C ρ H a w hData hcalc p hWeak
  have hR := eventually_referenceRotationStrongDirichletFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc i j p hStrong
  have hi := referenceRotationStrongInvertibleLocus_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc i j p hStrong
  have hc := contDiffAt_referenceRotationSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (0,p) hi
  apply hc.congr_of_eventuallyEq
  filter_upwards [hS,hW,hR] with t htS htW htR
  exact (referenceRotationSharpRadialTraceFamily_eq_orthogonal
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t.1 t.2 htS htW htR).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSharpRadialTraceFamily_eq_orthogonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSharpRadialTraceFamily_coordinate_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceOrthogonalSharpRadialTraceFamily_joint_zero_angle

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_snd_mem_of_isOpen

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_referenceStrongDriftFamily_zero_isInvertible_product

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_referenceWeakDirichletEnergyFamily_isInvertible_product
