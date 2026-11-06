import Calderon.ActualFiveHalfDensityFirstInRoom
import Calderon.ActualFiniteGaugeDensityFirstSectionSupport
import Calderon.ActualSameFiveHalfSourceCoreApprox

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier SmoothMetricFrame
attribute [local irreducible] referenceRadialEndpointInvertibleLocus referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  referenceFiveHalfAdjointCoordinateBoundaryFamily referenceHighAdjointCoordinateBoundaryFamily
  ReferenceJacobiCompactExtensionRoom.fiveHalfMultiplierFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)

attribute [local irreducible] referenceFiveHalfAdjointJacobiBoundaryInRoom

attribute [local irreducible] referenceFiveHalfAdjointMovingBoundaryInRoom referenceFiveHalfHorizontalAngularL referenceMetricGramFrame

open ActualFiniteHarmonicCore
variable {KG : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
attribute [local irreducible] referenceFiveHalfDensityFirstActionInRoom referenceFiniteGaugeDensityFirstSection
  referenceHighDensityFirstAction sphereSobolevInclusionL sphereSobolevPartialSumL

lemma referenceFiniteGaugeDensityFirstSection_eq_fiveHalfInRoom_of_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (n : ℕ) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (i : Fin 3)
    (hGraph :
      (fun y => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
        (referenceFiniteGaugeDensityFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R
            (fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z)) y i)) =
      (fun y => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n
            (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z))) y i))
    (hRoom : ∀ y ∈ tsupport u, (q,(y,R y)) ∈ K ∧
      (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    (fun y => referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R
        (fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z)) y i) =
    (fun y => referenceFiveHalfDensityFirstActionInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y i) := by
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let v : R3 → SphereSobolev (3/2:ℝ) := fun y => Iin (u y)
  let un : R3 → SphereSobolev (5/2:ℝ) := fun y => sphereSobolevPartialSumL (5/2:ℝ) n (u y)
  let oldeta : R3 → SphereSobolev (3/2:ℝ) := fun y => referenceFiniteGaugeDensityFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v y i
  let neweta : R3 → SphereSobolev (3/2:ℝ) := fun y => referenceFiveHalfDensityFirstActionInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R un y i
  have hVSupp : tsupport v ⊆ tsupport u := tsupport_comp_subset (map_zero Iin) u
  have hnSupp : tsupport un ⊆ tsupport u :=
    tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (5/2:ℝ) n)) u
  have hOldSupp : tsupport oldeta ⊆ tsupport u :=
    (tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R v i).trans hVSupp
  have hNewSupp : tsupport neweta ⊆ tsupport u :=
    (tsupport_referenceFiveHalfDensityFirstActionInRoom_subset
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 q R un i).trans hnSupp
  have hCut : (fun y => Iin (un y)) =
      (fun y => sphereSobolevPartialSumL (3/2:ℝ) n (v y)) :=
    funext (fun y => sphereSobolevInclusionL_sphereSobolevPartialSumL_fiveHalf n (u y))
  change oldeta = neweta
  funext y
  by_cases hy : y ∈ tsupport u
  · apply sphereSobolevInclusionL_injective (3/2:ℝ) (1/2:ℝ) (by norm_num)
    have hOld := congrFun hGraph y
    have hNew := referenceDensityFirstActionInRoom_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg q R un y i
        ((contDiff_sphereSobolevPartialSumL_fiveHalf u hu n).contDiffAt.differentiableAt (by simp))
        (hRoom y hy).1 (hRoom y hy).2
    have hX := congrArg (fun f : R3 → SphereSobolev (3/2:ℝ) =>
      referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R f y i) hCut
    exact hOld.trans (hX.symm.trans hNew.symm)
  · have hOldZero : oldeta y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (hOldSupp h))
    have hNewZero : neweta y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (hNewSupp h))
    exact hOldZero.trans hNewZero.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
