import Calderon.ActualConstantOneLeadingFirstHalf
import Calderon.ConstantFirstSectionCovariantAlgebra
import Calderon.ActualPhysicalHalfFirstSectionGraphDictionary
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift ConstantFirstSectionCovariantAlgebra
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referencePhysicalDensityHalfFromFirstSections
  referenceHighDensityFirstAction referenceHighHorizontalAction referenceHighHorizontalAngularL
  referenceHighAdjointMovingBoundaryActionFamily referenceMetricGramFrame referenceFrameConnectionCoefficient
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint sphereSobolevInclusionL
  referenceNativeMovingAdjointParametricCorrection referenceHighAdjointMovingDifferenceQuotient
  constantOneFirstRaisingThreeHalf constantOneDoubleRaisingHalf

private lemma original_high_first_add
    (q : ℝ) (R : R3 → ℝ) (u v : R3 → SphereSobolev (3/2:ℝ)) (y : R3) (i : Fin 3)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => u z+v z) y i =
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i+
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i := by
  have hD := fderiv_fun_add hu hv
  delta referenceHighDensityFirstAction referenceHighHorizontalAction
  simp only [hD,ContinuousLinearMap.add_apply,map_add]
  abel

theorem referencePhysicalDensityHalfFromFirstSections_constant_leading_decomposition
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (hr : R y ≠ 0)
    (kappa : Fin 3 → R3 → SphereSobolev (3/2:ℝ))
    (hkappa : ∀ j : Fin 3, ContDiffAt ℝ ∞ (kappa j) y) :
    let V : Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun j z => (R z)⁻¹ • constantOneFirstRaisingThreeHalf hF j
    let eta : Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun j z => V j z+kappa j z
    let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j
    let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
    let Reg := fun i j : Fin 3 =>
      I (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ)
        ((q,y),fderiv ℝ R y) i (constantOneFirstRaisingThreeHalf hF j)) +
      R y • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (constantOneFirstRaisingThreeHalf hF j) +
      R y • referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (kappa j) y i -
      R y • (∑ k : Fin 3, Gamma i j k • I (kappa k y))
    let Drift := fun i : Fin 3 => I (constantOneFirstRaisingThreeHalf hF i)+R y • I (kappa i y)
    referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R eta y =
      (R y)⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, (Q i j-(if i=j then (1:ℝ) else 0)) • constantOneDoubleRaisingHalf hF i j) +
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Reg i j) +
      (∑ i : Fin 3, b i • Drift i) := by
  intro V eta I Q Gamma b Reg Drift
  let Cov := fun i j : Fin 3 => referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (eta j) y i-
    ∑ k : Fin 3, Gamma i j k • I (eta k y)
  have hP : referencePhysicalDensityHalfFromFirstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R eta y =
      R y • ((∑ i : Fin 3, ∑ j : Fin 3, Q i j • Cov i j)+(∑ i : Fin 3, b i • I (eta i y))) := by
    delta referencePhysicalDensityHalfFromFirstSections
    exact Eq.refl _
  have hRCov (i j : Fin 3) : R y • Cov i j = (R y)⁻¹ • constantOneDoubleRaisingHalf hF i j+Reg i j := by
    have hDiffV : DifferentiableAt ℝ (V j) y :=
      ((hR.differentiable (by simp) y).inv hr).smul_const (constantOneFirstRaisingThreeHalf hF j)
    have hAdd := original_high_first_add g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R (V j) (kappa j) y i hDiffV ((hkappa j).differentiableAt (by simp))
    have hFirst := congrArg (fun value : SphereSobolev (1/2:ℝ) =>
      R y • (value-∑ k : Fin 3, Gamma i j k • I (eta k y))) hAdd
    have hSplit := radius_smul_covariant_split I (R y) hr
      (constantOneFirstRaisingThreeHalf hF) (fun k : Fin 3 => kappa k y) (Gamma i j)
      (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (V j) y i)
      (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (kappa j) y i)
    have hLeading := referenceConstantOneLeadingHighFirstAction_covariant_half_decomposition
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy i j hr
    have hReplace := congrArg (fun leading : SphereSobolev (1/2:ℝ) => leading+
      (R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (kappa j) y i-
       R y • (∑ k : Fin 3, Gamma i j k • I (kappa k y)))) hLeading
    have hRegroup := regroup_leading_regular_terms ((R y)⁻¹ • constantOneDoubleRaisingHalf hF i j)
      (I (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ)
        ((q,y),fderiv ℝ R y) i (constantOneFirstRaisingThreeHalf hF j)))
      (R y • referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (constantOneFirstRaisingThreeHalf hF j))
      (R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (kappa j) y i)
      (R y • (∑ k : Fin 3, Gamma i j k • I (kappa k y)))
    exact hFirst.trans (hSplit.trans (hReplace.trans hRegroup))
  have hRFirst (i : Fin 3) : R y • I (eta i y)=Drift i :=
    radius_smul_inclusion_inverse_add I (R y) hr (constantOneFirstRaisingThreeHalf hF i) (kappa i y)
  have hScale := radius_smul_physical_sum I (R y) Q b Cov (fun i : Fin 3 => eta i y)
  have hReplaceSums :
      ((∑ i : Fin 3, ∑ j : Fin 3, Q i j • (R y • Cov i j))+
        (∑ i : Fin 3, b i • (R y • I (eta i y)))) =
      ((∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((R y)⁻¹ • constantOneDoubleRaisingHalf hF i j+Reg i j))+
        (∑ i : Fin 3, b i • Drift i)) := congrArg₂ (fun x z : SphereSobolev (1/2:ℝ) => x+z)
    (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => congrArg (fun value => Q i j • value) (hRCov i j))))
    (Finset.sum_congr rfl (fun i _ => congrArg (fun value => b i • value) (hRFirst i)))
  have hPrincipalSplit := principal_sum_split (R y) Q (constantOneDoubleRaisingHalf hF) Reg
  have hSplitSums := congrArg (fun principal : SphereSobolev (1/2:ℝ) => principal+∑ i : Fin 3, b i • Drift i) hPrincipalSplit
  have hSigma := sum_sub_kronecker_smul_of_diagonal_zero Q (constantOneDoubleRaisingHalf hF)
    (sum_constantOneDoubleRaisingHalf_diagonal_eq_zero hF hO hD)
  have hSigmaSums := congrArg (fun principal : SphereSobolev (1/2:ℝ) =>
    (R y)⁻¹ • principal+(∑ i : Fin 3, ∑ j : Fin 3, Q i j • Reg i j)+(∑ i : Fin 3, b i • Drift i)) hSigma
  exact hP.trans (hScale.trans (hReplaceSums.trans (hSplitSums.trans hSigmaSums)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
