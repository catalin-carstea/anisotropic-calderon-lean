import Calderon.ActualReferenceSmoothMultiplierJointTopology
import Calderon.ActualReferenceSmoothMultiplierExtensionIndependence
import Calderon.FiniteDimensionalLocalSmoothExtension

/-! Smooth boundary data transfers to the commutator; arbitrary chosen bulk
jets need not be smooth. -/
set_option autoImplicit false
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricVolume NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily
  referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily

lemma contDiffAt_referenceSmoothMultiplierBoundaryCommutator_of_joint_on_open
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (f : (ℝ × (R3 × ℝ)) × R3 → ℝ) (S : Set ((ℝ × (R3 × ℝ)) × R3)) (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (Q : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3)
    (hQValue : ∀ p, (∀ x : UnitSphere, (p,x.val) ∈ S) → ∀ x : UnitSphere,
      smoothSphereValue (nativeH2CoefficientSmoothData (Q p)) x = f (p,x.val))
    (p0 : ℝ × (R3 × ℝ)) (hCover : ∀ x : UnitSphere, (p0,x.val) ∈ S)
    (hRoom : p0 ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun p => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (Q p) p) p0 := by
  let K0 : Set ((ℝ × (R3 × ℝ)) × R3) := {p0} ×ˢ sphere (0 : R3) 1
  have hK0 : IsCompact K0 := isCompact_singleton.prod (isCompact_sphere _ _)
  have hK0S : K0 ⊆ S := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hp0 : p = p0 := Set.mem_singleton_iff.mp hp
    rw [hp0]
    exact hCover ⟨z,hz⟩
  obtain ⟨m,hm,hmc,hEq⟩ :=
    exists_contDiff_eq_near_compact_of_contDiffOn K0 S hK0 hS hK0S f hf
  let K : Set R3 := Prod.snd '' tsupport m
  have hK : IsCompact K := hmc.image continuous_snd
  have hz : ∀ p x, x ∉ K → m (p,x) = 0 := by
    intro p x hOutside
    by_contra hn
    exact hOutside ⟨(p,x),subset_tsupport m hn,rfl⟩
  have hRoomFields := hRoom
  unfold referenceRadialEndpointInvertibleLocus at hRoomFields
  have hSmoothJoint := contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData m hm K hK hz hcalc hF hO hD τ0 p0 p0 hRoomFields.1 hRoomFields.2.1
  have hDiagonal : ContDiffAt ℝ ∞
      (fun p : ℝ × (R3 × ℝ) => (p,p)) p0 := contDiffAt_id.prodMk contDiffAt_id
  have hSmooth : ContDiffAt ℝ ∞ (fun p => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 3 m hm K hK hz p) p) p0 :=
    by
      simpa only [Function.comp_def] using
        hSmoothJoint.comp (f := fun p : ℝ × (R3 × ℝ) => (p,p)) p0 hDiagonal
  have hNear : ∀ᶠ p in 𝓝 p0, ∀ z ∈ sphere (0 : R3) 1, m (p,z) = f (p,z) := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hEq (p0,z) ⟨rfl,hz⟩
  have hIn : ∀ᶠ p in 𝓝 p0, ∀ z ∈ sphere (0 : R3) 1, (p,z) ∈ S := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hS.mem_nhds (hCover ⟨z,hz⟩)
  have hRoomNear : ∀ᶠ p in 𝓝 p0, p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    (isOpen_referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hRoom
  apply hSmooth.congr_of_eventuallyEq
  filter_upwards [hNear,hIn,hRoomNear] with p hp hin hi
  unfold referenceRadialEndpointInvertibleLocus at hi
  apply referenceSmoothMultiplierBoundaryCommutatorFamily_eq_of_sphereValue_eq
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel
    (Q p) (commonSupportCoefficientFamily 3 m hm K hK hz p)
  · apply ContinuousMap.ext
    intro x
    change smoothSphereValue (nativeH2CoefficientSmoothData (Q p)) x =
      coefficientValue 3 (commonSupportCoefficientFamily 3 m hm K hK hz p) x.val
    rw [coefficientValue_commonSupportCoefficientFamily]
    exact (hQValue p (fun z => hin z.val z.property) x).trans (hp x.val x.property).symm
  · exact hi.1
  · exact hi.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSmoothMultiplierBoundaryCommutator_of_joint_on_open
