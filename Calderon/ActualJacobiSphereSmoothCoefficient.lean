import Calderon.ActualJacobiNativeCenterTrace
import Calderon.LocalSmoothAmbientExtension
import Calderon.NativeCoefficientFluxTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame

/-! These are the actual Jacobi coefficients. -/

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem exists_referenceJacobiSphereCoefficient_smoothJets
    (q : ℝ) (y : R3) (r : ℝ) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    ∃ F : SmoothCoefficientJets 2,
      smoothSphereValue (coefficientSmoothData F) =
        referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let E : R3 → ReferenceEndpointVariables := fun z => (q,((y,r),z))
  have hE : ContDiff ℝ ∞ E := contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  let J : R3 → R3 →L[ℝ] R3 := fun z => referenceFramedNormalizedJacobian g L Φ (E z)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ).comp hE
  let S : Set R3 := {z | (J z).IsInvertible}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    exact hJ.continuous.continuousAt.eventually hz.eventually_nhds
  have hKS : sphere (0 : R3) 1 ⊆ S := by
    intro z hz
    exact hInv ⟨z,hz⟩
  let f : R3 → ℝ := fun z => referenceFramedJacobiVelocityRemainder g L Φ i (E z) j
  have hf : ContDiffOn ℝ ∞ f S := by
    intro z hz
    exact (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.contDiffAt).comp z
      ((contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hΘ i (E z) hz).comp z
        hE.contDiffAt)).contDiffWithinAt
  obtain ⟨v,hvCompact,hvNear⟩ := exists_smoothData_eq_near_compact
    (sphere (0 : R3) 1) S (isCompact_sphere _ _) hS hKS f hf
  let F : SmoothCoefficientJets 2 := compactCoefficient 2 v.1 v.2 hvCompact
  have hF : coefficientSmoothData F = v := by
    apply Subtype.ext
    exact coefficientValue_compactCoefficient 2 v.1 v.2 hvCompact
  refine ⟨F,?_⟩
  rw [hF]
  ext x
  exact (hvNear x.val x.property).eq_of_nhds

def referenceJacobiBoundaryCoefficientJets
    (q : ℝ) (y : R3) (r : ℝ) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    SmoothCoefficientJets 2 :=
  Classical.choose (exists_referenceJacobiSphereCoefficient_smoothJets
    g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)

theorem smoothSphereValue_referenceJacobiBoundaryCoefficientJets
    (q : ℝ) (y : R3) (r : ℝ) (i j : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val))).IsInvertible) :
    smoothSphereValue (coefficientSmoothData
      (referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)) =
        referenceJacobiSphereCoefficient g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv :=
  Classical.choose_spec (exists_referenceJacobiSphereCoefficient_smoothJets
    g hg L y0 Φ B ε C ρ H a w hData q y r i j hInv)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobiSphereCoefficient_smoothJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJacobiBoundaryCoefficientJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSphereValue_referenceJacobiBoundaryCoefficientJets
