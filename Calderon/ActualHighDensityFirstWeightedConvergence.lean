import Calderon.FirstOrderWeightedL2JetPropagation
import Calderon.ActualCovariantDensityFirstActions

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral

private def highCoefficientSum {F : Type*} [AddCommGroup F] (a b : F) : F := a+b
private lemma contDiffAt_highCoefficientSum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : R3 → F) (y : R3) (ha : ContDiffAt ℝ ∞ a y) (hb : ContDiffAt ℝ ∞ b y) :
    ContDiffAt ℝ ∞ (fun z => highCoefficientSum (a z) (b z)) y := ha.add hb

private lemma threeHalf_derivative_frame_coordinates
    (T : R3 →L[ℝ] SphereSobolev (3/2:ℝ)) (e : R3) :
    T e = ∑ k : Fin 3, e k • T (EuclideanSpace.single k 1) := by
  have hSum : (∑ k : Fin 3, e k • EuclideanSpace.single k 1) = e := by
    ext j
    simp [Pi.single_apply]
  have h := congrArg T hSum
  simpa only [map_sum,map_smul] using h.symm

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAngularL referenceMetricGramFrame referenceRadialEndpointInvertibleLocus

private lemma highDensityFirstAction_coordinate_formula
    (q : ℝ) (R : R3 → ℝ) (v : R3 → SphereSobolev (3/2:ℝ)) (y : R3) (i : Fin 3) :
    referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i =
    (∑ k : Fin 3, ((referenceMetricGramFrame g L (q,y) i) k •
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
        (fderiv ℝ v y (EuclideanSpace.single k 1))) +
      highCoefficientSum (referenceHighHorizontalAngularL g L q y i)
        (referenceHighAdjointMovingBoundaryActionFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i) (v y) := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hFrame := congrArg I
    (threeHalf_derivative_frame_coordinates (fderiv ℝ v y) (referenceMetricGramFrame g L (q,y) i))
  simp only [map_sum,map_smul] at hFrame
  have hTerm : I (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) =
      ∑ k : Fin 3, ((referenceMetricGramFrame g L (q,y) i) k • I)
        (fderiv ℝ v y (EuclideanSpace.single k 1)) := by
    simpa only [ContinuousLinearMap.smul_apply] using hFrame
  have hDef : referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i =
      (I (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) +
        referenceHighHorizontalAngularL g L q y i (v y)) +
        referenceHighAdjointMovingBoundaryActionFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (v y) := rfl
  have hExpanded := hDef.trans (congrArg
    (fun z : SphereSobolev (1/2:ℝ) =>
      (z + referenceHighHorizontalAngularL g L q y i (v y)) +
        referenceHighAdjointMovingBoundaryActionFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (v y)) hTerm)
  simpa only [highCoefficientSum,ContinuousLinearMap.add_apply,add_assoc] using hExpanded

/-- The ORIGINAL high first action preserves the graph limits used for the
second word. Its original moving/radius/frame coefficients are retained. -/
theorem tendsto_integral_referenceHighDensityFirstAction_of_graph_limits
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (S : Set R3) (hS : IsCompact S)
    (U : ℕ → R3 → SphereSobolev (3/2:ℝ)) (u : R3 → SphereSobolev (3/2:ℝ))
    (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hu : ContDiff ℝ ∞ u)
    (hSuppU : ∀ n, tsupport (U n) ⊆ S) (hSuppu : tsupport u ⊆ S)
    (hGeometry : ∀ y ∈ S, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hValue : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖U n y - u y‖^2) atTop (𝓝 0))
    (hDerivative : ∀ X : R3, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖fderiv ℝ (U n) y X - fderiv ℝ u y X‖^2) atTop (𝓝 0)) (i : Fin 3) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (U n) y i -
        referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i‖^2)
      atTop (𝓝 0) := by
  let A : Fin 3 → R3 → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    fun k y => (referenceMetricGramFrame g L (q,y) i) k •
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Z : R3 → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun y =>
    highCoefficientSum (referenceHighHorizontalAngularL g L q y i)
      (referenceHighAdjointMovingBoundaryActionFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i)
  have hA (k : Fin 3) : ContDiff ℝ ∞ (A k) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp
      (contDiff_referenceMetricGramFrame_slice g hg L q i)).smul contDiff_const
  have hZ (y : R3) (hy : y ∈ S) : ContDiffAt ℝ ∞ Z y := by
    have hOmega := (contDiff_referenceHighHorizontalAngularL g hg L q i).contDiffAt (x := y)
    have hMove := (contDiffAt_referenceHighAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg R (q,y) i hR.contDiffAt
        (hGeometry y hy).1 (hGeometry y hy).2.2 (hGeometry y hy).2.1).comp y
          (contDiffAt_const.prodMk contDiffAt_id)
    exact contDiffAt_highCoefficientSum _ _ y hOmega hMove
  have h := tendsto_integral_firstOrder_of_value_and_derivative_tendsto
    g hg L q S hS U u hU hu hSuppU hSuppu A Z
      (fun k y hy => (hA k).continuous.continuousAt)
      (fun y hy => (hZ y hy).continuousAt) hValue hDerivative
  have hPoint (v : R3 → SphereSobolev (3/2:ℝ)) (y : R3) :
      referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i =
      (∑ k : Fin 3, A k y (fderiv ℝ v y (EuclideanSpace.single k 1))) + Z y (v y) :=
    highDensityFirstAction_coordinate_formula
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i
  have hSeq :
      (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
        ‖referenceHighDensityFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (U n) y i -
          referenceHighDensityFirstAction
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i‖^2) =
      (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
        ‖((∑ k : Fin 3, A k y (fderiv ℝ (U n) y (EuclideanSpace.single k 1))) + Z y (U n y)) -
          ((∑ k : Fin 3, A k y (fderiv ℝ u y (EuclideanSpace.single k 1))) + Z y (u y))‖^2) := by
    funext n
    have hErr : (fun y => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (U n) y i -
        referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) =
        (fun y => ((∑ k : Fin 3, A k y (fderiv ℝ (U n) y (EuclideanSpace.single k 1))) + Z y (U n y)) -
          ((∑ k : Fin 3, A k y (fderiv ℝ u y (EuclideanSpace.single k 1))) + Z y (u y))) :=
      funext (fun y => congrArg₂ (fun a b : SphereSobolev (1/2:ℝ) => a-b) (hPoint (U n) y) (hPoint u y))
    exact congrArg (fun f : R3 → SphereSobolev (1/2:ℝ) =>
      ∫ y, referenceDensityFamily g L (q,y) * ‖f y‖^2) hErr
  exact (congrArg (fun f : ℕ → ℝ => Tendsto f atTop (𝓝 (0:ℝ))) hSeq).mpr h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
