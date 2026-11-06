import Calderon.ActualPhysicalDensityOperatorSubtraction
import Calderon.ActualCutoffCommutatorSourceRoom
import Calderon.ActualSameCutoffNormalizedFiveHalfField

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift ActualFiniteHarmonicCore

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referencePhysicalDensityOperator referenceDensityScalarCutoffCommutator sphereSobolevInclusionL
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

theorem referencePhysicalDensityOperator_cutoff_sub_of_eq_zero
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R chi : R3 → ℝ)
    (Psi base : R3 → SphereSobolev (3/2:ℝ))
    (hPsi : ContDiff ℝ ∞ Psi) (hbase : ContDiff ℝ ∞ base) (hchi : ContDiff ℝ ∞ chi)
    (y : R3) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
      g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hEquation : referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R Psi y = 0) :
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (fun z => chi z • (Psi z-base z)) y =
      -(chi y • referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R base y) +
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceDensityScalarCutoffCommutator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi
            (fun z => Psi z-base z) y) := by
  have hSub := referencePhysicalDensityOperator_sub
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R Psi base
      hPsi hbase y hR hr hInv hp
  have hCut := referencePhysicalDensityOperator_smul_sub
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R chi
      (fun z => Psi z-base z) y (hPsi.sub hbase) hchi hR hr hInv hp
  have hForce : chi y • referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (fun z => Psi z-base z) y =
      -(chi y • referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R base y) := by
    rw [hSub,hEquation]
    simp only [zero_sub,smul_neg]
  exact (sub_eq_iff_eq_add.mp hCut).trans (by rw [hForce]; exact add_comm _ _)

/-- The extended density need solve its equation only on the cutoff support.
The inhomogeneous reference-section forcing remains explicit. -/
theorem referencePhysicalDensityOperator_cutoff_sub_global
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R chi : R3 → ℝ)
    (Psi base : R3 → SphereSobolev (3/2:ℝ))
    (hPsi : ContDiff ℝ ∞ Psi) (hbase : ContDiff ℝ ∞ base)
    (hchi : ContDiff ℝ ∞ chi) (hR : ContDiff ℝ ∞ R)
    (hGeometry : ∀ y ∈ tsupport chi, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hEquation : ∀ y ∈ tsupport chi, referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R Psi y = 0) :
    (fun y => referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (fun z => chi z • (Psi z-base z)) y) =
    (fun y => -(chi y • referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R base y) +
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceDensityScalarCutoffCommutator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi
            (fun z => Psi z-base z) y)) := by
  have hSourceSupp : tsupport (fun z => chi z • (Psi z-base z)) ⊆ tsupport chi :=
    tsupport_smul_subset_left chi (fun z => Psi z-base z)
  have hPSupp := (tsupport_referencePhysicalDensityOperator_subset
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
      (fun z => chi z • (Psi z-base z))).trans hSourceSupp
  funext y
  by_cases hy : y ∈ tsupport chi
  · exact referencePhysicalDensityOperator_cutoff_sub_of_eq_zero
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R chi Psi base
        hPsi hbase hchi y hR.contDiffAt (hGeometry y hy).1
          (hGeometry y hy).2.2 (hGeometry y hy).2.1 (hEquation y hy)
  · have hPZero : referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
          (fun z => chi z • (Psi z-base z)) y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hPSupp h))
    have hchiZero : chi y = 0 := image_eq_zero_of_notMem_tsupport hy
    have hDerivOutside : y ∉ tsupport (fderiv ℝ chi) :=
      fun h => hy (tsupport_fderiv_subset ℝ h)
    have hCommZero := referenceDensityScalarCutoffCommutator_eq_zero_of_notMem_derivative_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi
        (fun z => Psi z-base z) y hDerivOutside
    simp only [hPZero,hchiZero,hCommZero,zero_smul,neg_zero,map_zero,add_zero]

/-- The exact original normalized source, with its literal Sobolev one and the
FULL minus-chi-P-one forcing. -/
theorem referencePhysicalDensityOperator_normalizedSource_eq_cutoff_rhs
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R chi : R3 → ℝ)
    (Psi : R3 → SphereSobolev (3/2:ℝ)) (hPsi : ContDiff ℝ ∞ Psi)
    (hchi : ContDiff ℝ ∞ chi) (hR : ContDiff ℝ ∞ R)
    (hGeometry : ∀ y ∈ tsupport chi, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hEquation : ∀ y ∈ tsupport chi, referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R Psi y = 0) :
    (fun y => referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (normalizedThreeHalfSourceField chi Psi) y) =
    (fun y => -(chi y • referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
          (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y) +
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceDensityScalarCutoffCommutator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi
            (fun z => Psi z-sphereSobolevConstantOne (3/2:ℝ)) y)) := by
  exact referencePhysicalDensityOperator_cutoff_sub_global
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R chi Psi
      (fun _ => sphereSobolevConstantOne (3/2:ℝ)) hPsi contDiff_const hchi hR hGeometry hEquation

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
