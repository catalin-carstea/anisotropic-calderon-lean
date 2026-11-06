import Calderon.ActualHighAdjointMovingActualJetOrderedWords
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Metric
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma sq_smul_ordered_composition_sum
    (r f : ℝ) (T T1 : E →L[ℝ] V) (C0 : Fin 3 → E →L[ℝ] V)
    (Mi : E →L[ℝ] E) (M N : Fin 3 → E →L[ℝ] E) :
    r^2 • (T.comp Mi + (∑ j : Fin 3, (C0 j).comp (N j)) +
      r • (∑ j : Fin 3, T1.comp ((M j).comp (N j))) +
      r^2 • (∑ j : Fin 3, T.comp ((M j).comp (N j))) + (r*f) • T) =
    (r^2 • T).comp Mi + (∑ j : Fin 3, (C0 j).comp (r^2 • N j)) +
      (∑ j : Fin 3, T1.comp ((M j).comp (r^3 • N j))) +
      (∑ j : Fin 3, (r^2 • T).comp ((M j).comp (r^2 • N j))) +
      f • (r^3 • T) := by
  have h3 : r^2*r = r^3 := by ring
  have hf : r^2*(r*f) = f*r^3 := by ring
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_add, Finset.smul_sum, smul_smul, h3, hf]

end OAI.AnisotropicCalderon.DirichletFamily
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] referenceHighAdjointMovingActualJetNormalizedCorrection
  referenceHighAdjointRadialSecondRemainder referenceHighAdjointCoordinateBoundaryFamily
  referenceAdjointThreeHalfRadialFamily nativeThreeHalfCoefficientMulL
  referenceJacobiBoundaryThreeHalfCoefficientJets sphereSobolevLinearCoordinateMulL

lemma referenceHighAdjointMovingActualJetNormalizedCorrection_sq_smul_eq_ordered_words
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r f : ℝ) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let T := referenceHighAdjointRadialSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    let T1 := deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let M := fun j : Fin 3 => sphereSobolevLinearCoordinateMulL
      hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
    let C0 := fun j : Fin 3 => referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let N := fun j : Fin 3 => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryThreeHalfCoefficientJets
        g L y0 Φ B ε C ρ H a w hData hg q y r i j hInv)
    r^2 • referenceHighAdjointMovingActualJetNormalizedCorrection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r f i hInv =
    (r^2 • T).comp (M i) + (∑ j : Fin 3, (C0 j).comp (r^2 • N j)) +
      (∑ j : Fin 3, T1.comp ((M j).comp (r^3 • N j))) +
      (∑ j : Fin 3, (r^2 • T).comp ((M j).comp (r^2 • N j))) +
      f • (r^3 • T) := by
  intro T T1 M C0 N
  have hOriginal := referenceHighAdjointMovingActualJetNormalizedCorrection_eq_ordered_words
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q y r f i hInv hSegment
  have hWeighted := congrArg
    (fun F : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => r^2 • F)
    hOriginal
  have hAlgebra := sq_smul_ordered_composition_sum r f T T1 C0 (M i) M N
  exact hWeighted.trans hAlgebra

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.sq_smul_ordered_composition_sum
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingActualJetNormalizedCorrection_sq_smul_eq_ordered_words
