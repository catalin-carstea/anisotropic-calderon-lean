import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily
import Calderon.FiniteDimensionalLocalSmoothExtension

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-JACOBI-COMPACT-SMOOTH-EXTENSION-EXPANSION-v001.md. Same actual sphere coefficients, one smooth compact extension. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame
  NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem exists_contDiff_compact_referenceJacobiBoundaryThreeHalfCoefficient_extension
    (i j : Fin 3) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K)
    (hInv : ∀ p ∈ K, ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    ∃ m : (ℝ × (R3 × ℝ)) × R3 → ℝ, ContDiff ℝ ∞ m ∧ HasCompactSupport m ∧
      ∀ p ∈ K, ∀ᶠ t in 𝓝 p, ∀ x : UnitSphere,
        m (t,x.val) = coefficientValue 3
          (referenceJacobiBoundaryThreeHalfCoefficientFamily
            g hg L y0 Φ B ε C ρ H a w hData i j t) x.val := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let T : (ℝ × (R3 × ℝ)) × R3 → ReferenceEndpointVariables :=
    fun t => (t.1.1,(t.1.2,t.2))
  have hT : ContDiff ℝ ∞ T :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  let J : (ℝ × (R3 × ℝ)) × R3 → R3 →L[ℝ] R3 :=
    fun t => referenceFramedNormalizedJacobian g L Φ (T t)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ).comp hT
  let S : Set ((ℝ × (R3 × ℝ)) × R3) := {t | (J t).IsInvertible}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact hJ.continuous.continuousAt.eventually ht.eventually_nhds
  let f : (ℝ × (R3 × ℝ)) × R3 → ℝ :=
    fun t => referenceFramedJacobiVelocityRemainder g L Φ i (T t) j
  have hf : ContDiffOn ℝ ∞ f S := by
    intro t ht
    exact (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.contDiffAt).comp t
      ((contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hΘ i (T t) ht).comp t
        hT.contDiffAt)).contDiffWithinAt
  let K0 := K ×ˢ sphere (0 : R3) 1
  have hK0 : IsCompact K0 := hK.prod (isCompact_sphere _ _)
  have hK0S : K0 ⊆ S := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    exact hInv p hp ⟨x,hx⟩
  obtain ⟨m,hm,hmc,hEq⟩ := exists_contDiff_eq_near_compact_of_contDiffOn K0 S hK0 hS hK0S f hf
  refine ⟨m,hm,hmc,?_⟩
  intro p hp
  have hNear : ∀ᶠ t in 𝓝 p, ∀ z ∈ sphere (0 : R3) 1, m (t,z)=f (t,z) := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hEq (p,z) ⟨hp,hz⟩
  have hIn : ∀ᶠ t in 𝓝 p, ∀ z ∈ sphere (0 : R3) 1, (t,z) ∈ S := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hS.mem_nhds (hInv p hp ⟨z,hz⟩)
  filter_upwards [hNear,hIn] with t ht hin
  intro x
  have hOriginal : coefficientValue 3
      (referenceJacobiBoundaryThreeHalfCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData i j t) x.val = f (t,x.val) := by
    rw [referenceJacobiBoundaryThreeHalfCoefficientFamily,coefficientValue_compactCoefficient]
    change smoothSphereValue (coefficientSmoothData
      (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j t)) x = _
    rw [referenceJacobiBoundaryCoefficientFamily_eq
      g hg L y0 Φ B ε C ρ H a w hData i j t (fun z => hin z.val z.property),
      smoothSphereValue_referenceJacobiBoundaryCoefficientJets]
    rfl
  exact (ht x.val x.property).trans hOriginal.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_contDiff_compact_referenceJacobiBoundaryThreeHalfCoefficient_extension
