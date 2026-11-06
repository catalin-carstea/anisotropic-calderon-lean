import Calderon.ActualFiniteHighPrimalMovingTopology
import Calderon.ActualFiniteHighHorizontalSection

/-! Y = -H + Cprimal - div_mu(e) on the original finite input, with no Pdag domain premise. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHighPrimalMovingBoundaryFamily
  referenceFiniteHighHorizontalSection referenceHighHorizontalAction
  referenceHighMovingBoundaryActionFamily referenceMetricGramFrame
  referenceFrameConnectionCoefficient sphereSobolevPartialSumL sphereSobolevInclusionL

def referenceFiniteHighFullAdjointFirstSection
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i : Fin 3) : SphereSobolev (3/2 : ℝ) :=
  -referenceFiniteHighHorizontalSection g L hcalc hF hO hD τ0 n q u y i +
  referenceFiniteHighPrimalMovingBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R y i (u y) -
  (∑ j : Fin 3, referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) j) j i) •
      sphereSobolevPartialSumL (3/2 : ℝ) n (u y)

lemma sphereSobolevInclusionL_referenceFiniteHighFullAdjointFirstSection
    (hreg : FixedDirichletRegularity) (n : ℕ) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : DifferentiableAt ℝ u y) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,(y,R y)),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,R y)),z)‖ ≤ lam/4) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteHighFullAdjointFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i) =
    -referenceHighHorizontalAction g L q
      (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) y i +
    referenceHighMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
        (sphereSobolevPartialSumL (3/2 : ℝ) n (u y)) -
    (∑ j : Fin 3, referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) j) j i) •
        sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (sphereSobolevPartialSumL (3/2 : ℝ) n (u y)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let delta := ∑ j : Fin 3, referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) j) j i
  let v := sphereSobolevPartialSumL (3/2 : ℝ) n (u y)
  have hHorizontal := sphereSobolevInclusionL_referenceFiniteHighHorizontalSection
    g L hcalc hF hO hD τ0 n q u y i hu
  have hMoving := sphereSobolevInclusionL_referenceFiniteHighPrimalMovingBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg n q R y i lam Lam hUE hsmall (u y)
  have hScalar : I (delta • v) = delta • I v := I.map_smul delta v
  have hCombined := congrArg₂ (fun x z : SphereSobolev (1/2 : ℝ) => x-z)
    (congrArg₂ (fun x z : SphereSobolev (1/2 : ℝ) => -x+z) hHorizontal hMoving) hScalar
  simpa only [referenceFiniteHighFullAdjointFirstSection,map_add,map_sub,map_neg,
    sphereSobolevPartialSumL_apply,I,delta,v] using hCombined

lemma contDiffAt_referenceFiniteHighFullAdjointFirstSection
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i : Fin 3) (hu : ContDiffAt ℝ ∞ u y)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hi : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => referenceFiniteHighFullAdjointFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u x i) y := by
  have hHorizontal := contDiffAt_referenceFiniteHighHorizontalSection
    g hg L hcalc hF hO hD τ0 n q u y i hu
  have hMoving := (contDiffAt_referenceFiniteHighPrimalMovingBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R y i hR hr hInv hi).clm_apply hu
  have hPartial : ContDiffAt ℝ ∞ (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) y :=
    (sphereSobolevPartialSumL (3/2 : ℝ) n).contDiff.contDiffAt.comp y hu
  have hDivergence : ContDiffAt ℝ ∞ (fun x => ∑ j : Fin 3,
      referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) j) j i) y := by
    apply ContDiffAt.sum
    intro j hj
    exact (AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field g hg L q
      (fun x => referenceMetricGramFrame g L (q,x) j)
      (contDiff_referenceMetricGramFrame_slice g hg L q j) j i).contDiffAt
  simpa (config := { instances := true }) only
    [referenceFiniteHighFullAdjointFirstSection,Pi.add_def,Pi.sub_def,Pi.neg_def,Pi.smul_def'] using
    ((hHorizontal.neg.add hMoving).sub (hDivergence.smul hPartial))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHighFullAdjointFirstSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteHighFullAdjointFirstSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteHighFullAdjointFirstSection
