import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore
import Calderon.ActualPhysicalDensityProductsWeightedAdjunction
import Calderon.FiniteOperatorProductsSmoothness
import Calderon.ActualPhysicalDensityProductsOperatorIdentities
import Calderon.PhysicalDensityProductsWeightedSumsSmoothness

/-! Actual Main M1 Products adjoint. No quantitative Productsdag cap, finite-output
assumption or intrinsic Half adjoint is used. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

set_option Elab.async false

lemma contDiffOn_referencePhysicalDensityProducts_weighted_sums
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let U : Set R3 := {y | R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
    let coeff : Fin 3 → Fin 3 → R3 → ℝ := fun i j x =>
      referenceDensityPrincipalFrameCoefficient g g2 L q x i j
    let Fh : Fin 3 → R3 → Hi →L[ℝ] Hi := fun i x =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
    let Fl : Fin 3 → R3 → Half →L[ℝ] Half := fun i x =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,x),fderiv ℝ R x) i
    let Fbh : Fin 3 → R3 → Hi →L[ℝ] Hi := fun i x =>
      referenceNativeMovingParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
    let Fbl : Fin 3 → R3 → Half →L[ℝ] Half := fun i x =>
      referenceNativeMovingParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,x),fderiv ℝ R x) i
    let Eh : Fin 3 → R3 → Hi →L[ℝ] Half := fun i x =>
      referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
    let Eb : Fin 3 → R3 → Hi →L[ℝ] Half := fun i x =>
      referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
    ContDiffOn ℝ ∞ (fun x : R3 => (R x)^2 •
      (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j x • ((Fl i x).comp (Eh j x)+(Eh i x).comp (Fh j x)))) U ∧
    ContDiffOn ℝ ∞ (fun x : R3 => (R x)^2 •
      (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j x • ((Eb j x).comp (Fbh i x)+(Fbl j x).comp (Eb i x)))) U := by
  classical
  intro Ω U coeff Fh Fl Fbh Fbl Eh Eb
  have hChi : ContDiff ℝ ∞ (fun x : R3 => (q,x)) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => q)).prodMk contDiff_id
  have hQ (i j : Fin 3) : ContDiff ℝ ∞ (coeff i j) := by
    have hJoint : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
        referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 i j) :=
      contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j
    have hRaw := hJoint.comp hChi
    simpa only [coeff,Function.comp_def] using hRaw
  have hDR : ContDiff ℝ ∞ (fderiv ℝ R) := by
    exact hR.fderiv_right (by simp)
  have hParam : ContDiff ℝ ∞ (fun x : R3 => ((q,x),fderiv ℝ R x)) :=
    (contDiff_const.prodMk contDiff_id).prodMk hDR
  have hFh (i : Fin 3) : ContDiff ℝ ∞ (Fh i) :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L (3/2 : ℝ) i).comp hParam
  have hFl (i : Fin 3) : ContDiff ℝ ∞ (Fl i) :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD g hg L (1/2 : ℝ) i).comp hParam
  have hFbh (i : Fin 3) : ContDiff ℝ ∞ (Fbh i) := by
    have hJoint := contDiff_referenceNativeMovingParametricCorrection_joint hF hO hD g hg L (3/2 : ℝ) i
    have hProfile := hJoint.comp hParam
    simpa only [Fbh,Function.comp_def] using hProfile
  have hFbl (i : Fin 3) : ContDiff ℝ ∞ (Fbl i) := by
    have hJoint := contDiff_referenceNativeMovingParametricCorrection_joint hF hO hD g hg L (1/2 : ℝ) i
    have hProfile := hJoint.comp hParam
    simpa only [Fbl,Function.comp_def] using hProfile
  let U0 : Set R3 := {y | R y ≠ 0 ∧ (q,(y,R y)) ∈ Ω ∧
    (∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
  have hSub : U ⊆ U0 := by
    intro y hy
    refine ⟨hy.1,?_,hy.2.2⟩
    have hEndpoint := hy.2.1 1 (by norm_num)
    simpa only [one_mul] using hEndpoint
  have hUnweightedOpen := contDiffOn_referenceHighAdjointMovingDifferenceQuotient_weighted_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR
  have hEH (i : Fin 3) : ContDiffOn ℝ ∞ (Eh i) U := by
    have hRaw := (hUnweightedOpen.2 0 i).mono hSub
    simpa only [pow_zero,one_smul,Eh] using hRaw
  have hEb (i : Fin 3) : ContDiffOn ℝ ∞ (Eb i) U :=
    (contDiffOn_referenceAdjointMovingDifferenceQuotientPivot
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR i).1
  have hProducts := contDiffOn_fin_three_weighted_operator_products
    U (fun x : R3 => (R x)^2) coeff Fh Fbh Fl Fbl Eh Eb
    (hR.pow 2).contDiffOn (fun i j => (hQ i j).contDiffOn)
    (fun i => (hFh i).contDiffOn) (fun i => (hFbh i).contDiffOn)
    (fun i => (hFl i).contDiffOn) (fun i => (hFbl i).contDiffOn)
    hEH hEb
  exact hq.elim (fun _ _ => hProducts)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
