import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergyGerm
import Calderon.MixedKernelConstruction.MixedKernelProductPhases
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator
open scoped ContDiff Topology InnerProductSpace

/-- The literal metric criterion depends only on the actual physical first and second phase jets. -/
theorem productHessianStrictAt_congr_of_eventuallyEq
    (g1 g2 : MatrixField) (x y : R3) (rho tau : R3 × R3 → ℝ)
    (hEq : rho=ᶠ[𝓝 (x,y)]tau) :
    ProductHessianStrictAt g1 g2 x y rho ↔ ProductHessianStrictAt g1 g2 x y tau := by
  have hFirst : fderiv ℝ rho (x,y)=fderiv ℝ tau (x,y) := hEq.fderiv_eq
  have hSecond : fderiv ℝ (fderiv ℝ rho) (x,y)=fderiv ℝ (fderiv ℝ tau) (x,y) := hEq.fderiv.fderiv_eq
  unfold ProductHessianStrictAt
  rw [hFirst,hSecond]

/-- The ONE actual global energy has exactly the same strictness test as the SAME differentiated packet energy. -/
theorem productHessianStrictAt_nativeGlobalEnergy_iff
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ)
    (i : Fin C.count) (y : R3) (hy : y ∈ (C.packet i).centers)
    (hrR : referenceRadius delta Rstar p L y<R) (z : R3) (hz : ‖z‖=1)
    (rho : R3 × R3 → ℝ)
    (hFamily : ∀ᶠ a : R3 × R3 in 𝓝 (y,z),
      rho (packetEndpoint S L (C.packet i) lam a.1 (referenceRadius delta Rstar p L y) a.2,a.1)=
        (⟪a.2,a.2⟫_ℝ-1)/2)
    (g1 g2 : MatrixField) :
    let x := packetEndpoint S L (C.packet i) lam y (referenceRadius delta Rstar p L y) z
    ProductHessianStrictAt g1 g2 x y (nativeGlobalEnergy S L C lam R delta Rstar p) ↔
      ProductHessianStrictAt g1 g2 x y
        (nativeEnergyPhase (referenceRadius delta Rstar p L y) rho (referenceRadius delta Rstar p L)) := by
  intro x
  exact productHessianStrictAt_congr_of_eventuallyEq g1 g2 x y _ _
    (nativeGlobalEnergy_eventuallyEq_nativeEnergyPhase S L C lam hlam R hR hRoom delta Rstar hd hRs p i y hy hrR z hz rho hFamily)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
