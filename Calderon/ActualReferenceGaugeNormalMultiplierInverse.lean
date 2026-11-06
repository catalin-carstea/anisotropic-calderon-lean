import Calderon.ActualReferenceGaugeBoundaryCoefficientFamilies
import Calderon.ActualReferenceGaugeBoundaryFactorization
import Calderon.NativeSmoothMultiplierInverse
import Calderon.FiniteDimensionalLocalSmoothExtension

/-! Actual positive normal coefficient,
compact reciprocal room, and native half/negative-half inverses. No weighted DN inverse. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  MetricVolume SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeHalfSmoothMultiplier NativeNegativeHalfSmoothMultiplier NativeSmoothMultiplierInverse

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

include hData hg

theorem isOpen_referenceGaugeNormalCoefficient_posLocus :
    IsOpen {p : (ℝ × (R3 × ℝ)) × R3 | 0 < referenceGaugeNormalCoefficient g L Φ a p} :=
  isOpen_lt continuous_const
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg).continuous

theorem exists_referenceGaugeNormalCoefficient_compact_reciprocal
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ∃ n : (ℝ × (R3 × ℝ)) × R3 → ℝ, ContDiff ℝ ∞ n ∧ HasCompactSupport n ∧
      (∀ p ∈ Q, ∀ x : UnitSphere,
        n (p,x.val) = (referenceGaugeNormalCoefficient g L Φ a (p,x.val))⁻¹) ∧
      (∀ v ∈ Q ×ˢ sphere (0 : R3) 1,
        ∀ᶠ u in 𝓝 v, n u = (referenceGaugeNormalCoefficient g L Φ a u)⁻¹) := by
  let K : Set ((ℝ × (R3 × ℝ)) × R3) := Q ×ˢ sphere (0 : R3) 1
  let S : Set ((ℝ × (R3 × ℝ)) × R3) :=
    {p | 0 < referenceGaugeNormalCoefficient g L Φ a p}
  have hK : IsCompact K := hQ.prod (isCompact_sphere _ _)
  have hS : IsOpen S :=
    isOpen_referenceGaugeNormalCoefficient_posLocus g L Φ y0 B ε C ρ H a w hData hg
  have hKS : K ⊆ S := by
    intro p hp
    exact referenceGaugeNormalCoefficient_sphere_pos
      g L Φ a y0 B ε C ρ H w hData p.1 ⟨p.2,hp.2⟩
  have hInv : ContDiffOn ℝ ∞
      (fun p => (referenceGaugeNormalCoefficient g L Φ a p)⁻¹) S := by
    apply (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg).contDiffOn.inv
    intro p hp
    exact ne_of_gt hp
  obtain ⟨n,hn,hnc,hEq⟩ := exists_contDiff_eq_near_compact_of_contDiffOn K S hK hS hKS
    (fun p => (referenceGaugeNormalCoefficient g L Φ a p)⁻¹) hInv
  refine ⟨n,hn,hnc,?_,hEq⟩
  intro p hp x
  exact (hEq (p,x.val) ⟨hp,x.property⟩).eq_of_nhds

def referenceGaugeNormalHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p)

def referenceGaugeNormalNegativeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p)

theorem contDiff_referenceGaugeNormalHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData)

theorem contDiff_referenceGaugeNormalNegativeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0) :=
  contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData)

theorem referenceGaugeNormalMultiplierFamilies_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).IsInvertible ∧
    (referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).IsInvertible := by
  let F := referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p
  let m := coefficientSmoothData F
  obtain ⟨M,hM,hm,hgrad⟩ := exists_smooth_ball_multiplier_bound m
  have hpos : ∀ x : UnitSphere, 0 < m.1 x.val := by
    intro x
    change 0 < coefficientValue 2
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p) x.val
    rw [coefficientValue_referenceGaugeNormalCoefficientJetsFamily]
    exact referenceGaugeNormalCoefficient_sphere_pos g L Φ a y0 B ε C ρ H w hData p x
  obtain ⟨n,N,hN,hn,hgn,_,_,hHalf,hHalf',hNeg,hNeg'⟩ :=
    exists_nativeSmoothMulL_two_sided_inverse hF hO hD τ0 m hM hm hgrad hpos
  have hHalfEq := nativeHalfCoefficientMulL_eq_smoothMulL
    hcalc hF hO hD τ0 F hM hm hgrad
  have hNegEq := nativeNegativeHalfCoefficientMulL_eq_smoothMulL
    hcalc hF hO hD τ0 F hM hm hgrad
  change (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F).IsInvertible ∧
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).IsInvertible
  rw [hHalfEq,hNegEq]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hHalf hHalf',
    ContinuousLinearMap.IsInvertible.of_inverse hNeg hNeg'⟩

theorem contDiff_referenceGaugeNormalHalfMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceGaugeNormalMultiplierFamilies_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).1.contDiffAt_map_inverse.comp p
      (contDiff_referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).contDiffAt

theorem contDiff_referenceGaugeNormalNegativeHalfMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceGaugeNormalNegativeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceGaugeNormalMultiplierFamilies_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).2.contDiffAt_map_inverse.comp p
      (contDiff_referenceGaugeNormalNegativeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).contDiffAt

attribute [local irreducible] referenceGaugeNormalHalfMultiplierFamily
  referenceGaugeNormalNegativeHalfMultiplierFamily


end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.isOpen_referenceGaugeNormalCoefficient_posLocus
#print axioms OAI.AnisotropicCalderon.ConnectionError.exists_referenceGaugeNormalCoefficient_compact_reciprocal
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalNegativeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalNegativeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalMultiplierFamilies_isInvertible
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalHalfMultiplierFamily_inverse
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalNegativeHalfMultiplierFamily_inverse
