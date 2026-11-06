import Calderon.SupportedWeightedL2NullCalculus
import Calderon.ActualHighDensityFirstGlobalSupport
import Calderon.ActualFiniteGaugePhysicalDensityHalfSectionSmoothness

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

/-- Finite contraction with the connection subtraction retained explicitly. -/
def finiteSecondOrderContraction
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r : ℝ) (a : Fin 3 → Fin 3 → ℝ) (gam : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (b : Fin 3 → ℝ) (x : Fin 3 → Fin 3 → V) (z : Fin 3 → V) : V :=
  r • ((∑ i : Fin 3, ∑ j : Fin 3, a i j •
    (x i j - ∑ k : Fin 3, gam i k j • z k)) + ∑ i : Fin 3, b i • z i)

theorem finiteSecondOrderContraction_sub
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r : ℝ) (a : Fin 3 → Fin 3 → ℝ) (gam : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (b : Fin 3 → ℝ) (x x' : Fin 3 → Fin 3 → V) (z z' : Fin 3 → V) :
    finiteSecondOrderContraction r a gam b (fun i j => x i j - x' i j) (fun k => z k - z' k) =
      finiteSecondOrderContraction r a gam b x z - finiteSecondOrderContraction r a gam b x' z' := by
  have hSecond (i j : Fin 3) :
      (x i j - x' i j) - ∑ k : Fin 3, gam i k j • (z k - z' k) =
      (x i j - ∑ k : Fin 3, gam i k j • z k) -
        (x' i j - ∑ k : Fin 3, gam i k j • z' k) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    abel
  unfold finiteSecondOrderContraction
  simp only [hSecond,smul_sub,Finset.sum_sub_distrib]
  rw [←smul_sub]
  congr 1
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAngularL referenceMetricGramFrame referenceRadialEndpointInvertibleLocus
  referenceFramedNormalizedJacobian referenceFrameConnectionCoefficient
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint sphereSobolevInclusionL

/-- The complete physical contraction of higher first sections, with the
original outside radius, connection subtraction, metric and drift terms. -/
def referencePhysicalDensityHalfFromFirstSections
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (eta : Fin 3 → R3 → SphereSobolev (3/2:ℝ)) (y : R3) : SphereSobolev (1/2:ℝ) :=
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  R y • ((∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (eta j) y i -
        ∑ k : Fin 3, referenceFrameConnectionCoefficient
          g L q y (referenceMetricGramFrame g L (q,y) i) k j • I (eta k y))) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • I (eta i y))

attribute [local irreducible] referencePhysicalDensityHalfFromFirstSections

/-- Actual first-section graph limits imply convergence of the complete
physical H1/2 lift. No constant uniform in the source or radius is asserted. -/
theorem tendsto_integral_referencePhysicalDensityHalfFromFirstSections
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (S : Set R3) (hS : IsCompact S)
    (Eta : ℕ → Fin 3 → R3 → SphereSobolev (3/2:ℝ))
    (eta : Fin 3 → R3 → SphereSobolev (3/2:ℝ))
    (hEta : ∀ n j, ContDiff ℝ ∞ (Eta n j)) (heta : ∀ j, ContDiff ℝ ∞ (eta j))
    (hSuppEta : ∀ n j, tsupport (Eta n j) ⊆ S) (hSuppeta : ∀ j, tsupport (eta j) ⊆ S)
    (hGeometry : ∀ y ∈ S, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hValue : ∀ j, Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖Eta n j y - eta j y‖^2) atTop (𝓝 0))
    (hDerivative : ∀ j (X : R3), Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖fderiv ℝ (Eta n j) y X - fderiv ℝ (eta j) y X‖^2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖referencePhysicalDensityHalfFromFirstSections
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R (Eta n) y -
        referencePhysicalDensityHalfFromFirstSections
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R eta y‖^2)
      atTop (𝓝 0) := by
  classical
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let X (u : R3 → SphereSobolev (3/2:ℝ)) (i : Fin 3) (y : R3) : SphereSobolev (1/2:ℝ) :=
    referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i
  let Gam (i k j : Fin 3) (y : R3) : ℝ := referenceFrameConnectionCoefficient
    g L q y (referenceMetricGramFrame g L (q,y) i) k j
  let A (i j : Fin 3) (y : R3) : ℝ := referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let b (i : Fin 3) (y : R3) : ℝ := normalizedSecondDriftFrameJoint g g2 L i (q,y)
  have hGam (i k j : Fin 3) : Continuous (Gam i k j) :=
    (AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field g hg L q
      (fun z => referenceMetricGramFrame g L (q,z) i)
      (contDiff_referenceMetricGramFrame_slice g hg L q i) k j).continuous
  have hA (i j : Fin 3) : Continuous (A i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hb (i : Fin 3) : Continuous (b i) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hBase (j : Fin 3) : SupportedWeightedL2Null g L q S (fun n y => Eta n j y - eta j y) := by
    refine ⟨fun n => (hEta n j).continuous.sub (heta j).continuous,?_,hValue j⟩
    intro n
    apply closure_minimal ?_ hS.isClosed
    intro y hy
    by_contra hOutside
    have hn : Eta n j y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hOutside (hSuppEta n j h))
    have hi : eta j y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hOutside (hSuppeta j h))
    exact hy (by simp only [hn,hi,sub_self])
  have hLow (j : Fin 3) : SupportedWeightedL2Null g L q S (fun n y => I (Eta n j y - eta j y)) :=
    SupportedWeightedL2Null.clm hg hS (hBase j) (fun _ => I) (fun _ _ => continuousAt_const)
  have hXSmooth (v : R3 → SphereSobolev (3/2:ℝ)) (hv : ContDiff ℝ ∞ v)
      (hs : tsupport v ⊆ S) (i : Fin 3) : ContDiff ℝ ∞ (X v i) :=
    contDiff_referenceHighDensityFirstAction_of_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR v hv
        (fun y hy => hGeometry y (hs hy)) i
  have hXSupp (v : R3 → SphereSobolev (3/2:ℝ)) (hs : tsupport v ⊆ S) (i : Fin 3) :
      tsupport (X v i) ⊆ S :=
    (tsupport_referenceHighDensityFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v i).trans hs
  have hWord (i j : Fin 3) : SupportedWeightedL2Null g L q S
      (fun n y => X (Eta n j) i y - X (eta j) i y) := by
    refine ⟨fun n => (hXSmooth _ (hEta n j) (hSuppEta n j) i).continuous.sub
      (hXSmooth _ (heta j) (hSuppeta j) i).continuous,?_,?_⟩
    · intro n
      apply closure_minimal ?_ hS.isClosed
      intro y hy
      by_contra hOutside
      have hn : X (Eta n j) i y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hOutside (hXSupp _ (hSuppEta n j) i h))
      have hi : X (eta j) i y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hOutside (hXSupp _ (hSuppeta j) i h))
      exact hy (by simp only [hn,hi,sub_self])
    · exact tendsto_integral_referenceHighDensityFirstAction_of_graph_limits
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR S hS
          (fun n => Eta n j) (eta j) (fun n => hEta n j) (heta j)
          (fun n => hSuppEta n j) (hSuppeta j) hGeometry (hValue j) (hDerivative j) i
  have hConn (i j : Fin 3) := SupportedWeightedL2Null.sum hg hS
    (fun k => fun n y => Gam i k j y • I (Eta n k y - eta k y))
    (fun k => SupportedWeightedL2Null.smul hg hS (hLow k) (Gam i k j)
      (fun y hy => (hGam i k j).continuousAt))
  have hSecond (i j : Fin 3) := SupportedWeightedL2Null.sub hg hS (hWord i j) (hConn i j)
  have hPrincipal := SupportedWeightedL2Null.sum hg hS
    (fun i => fun n y => ∑ j : Fin 3, A i j y •
      ((X (Eta n j) i y - X (eta j) i y) - ∑ k : Fin 3, Gam i k j y • I (Eta n k y - eta k y)))
    (fun i => SupportedWeightedL2Null.sum hg hS _
      (fun j => SupportedWeightedL2Null.smul hg hS (hSecond i j) (A i j)
        (fun y hy => (hA i j).continuousAt)))
  have hDrift := SupportedWeightedL2Null.sum hg hS
    (fun i => fun n y => b i y • I (Eta n i y - eta i y))
    (fun i => SupportedWeightedL2Null.smul hg hS (hLow i) (b i)
      (fun y hy => (hb i).continuousAt))
  have hTotal := SupportedWeightedL2Null.smul hg hS
    (SupportedWeightedL2Null.add hg hS hPrincipal hDrift) R
      (fun y hy => hR.continuous.continuousAt)
  have hPoint (n : ℕ) (y : R3) :
      R y • ((∑ i : Fin 3, ∑ j : Fin 3, A i j y •
        ((X (Eta n j) i y - X (eta j) i y) - ∑ k : Fin 3, Gam i k j y • I (Eta n k y - eta k y))) +
        ∑ i : Fin 3, b i y • I (Eta n i y - eta i y)) =
      referencePhysicalDensityHalfFromFirstSections
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R (Eta n) y -
      referencePhysicalDensityHalfFromFirstSections
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R eta y := by
    have hLinear := finiteSecondOrderContraction_sub
      (R y) (fun i j => A i j y) (fun i k j => Gam i k j y) (fun i => b i y)
      (fun i j => X (Eta n j) i y) (fun i j => X (eta j) i y)
      (fun k => I (Eta n k y)) (fun k => I (eta k y))
    simpa only [finiteSecondOrderContraction,referencePhysicalDensityHalfFromFirstSections,
      map_sub,I,X,A,Gam,b] using hLinear
  simpa only [hPoint] using hTotal.tendsto

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
