import Calderon.ActualReferenceGaugeNormalReciprocalGraph
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.SphereSobolevTangentialEndpointCompatibility

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/reciprocal-graph-author-v001/
EXPANSION-common-room-v002.md. One scalar, one open room, same genuine2/3 jets. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier

structure ReferenceGaugeNormalReciprocalRoom (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Q : Set (ℝ × (R3 × ℝ))) where
  scalar : (ℝ × (R3 × ℝ)) × R3 → ℝ
  smooth : ContDiff ℝ ∞ scalar
  jointCompactSupport : HasCompactSupport scalar
  spatialSupport : Set R3
  supportCompact : IsCompact spatialSupport
  zeroOutside : ∀ p z, z ∉ spatialSupport → scalar (p,z) = 0
  parameterRoom : Set (ℝ × (R3 × ℝ))
  roomOpen : IsOpen parameterRoom
  containsCompact : Q ⊆ parameterRoom
  near_eq : ∀ p ∈ parameterRoom, ∀ x : UnitSphere,
    ∀ᶠ v in 𝓝 (p,x.val), scalar v = (referenceGaugeNormalCoefficient g L Φ a v)⁻¹

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (y0 : R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

include hData hg in
lemma nonempty_referenceGaugeNormalReciprocalRoom
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    Nonempty (ReferenceGaugeNormalReciprocalRoom g L Φ a Q) := by
  obtain ⟨n,hn,hnc,hSphere,hNear⟩ := exists_referenceGaugeNormalCoefficient_compact_reciprocal
    g L Φ y0 B ε C ρ H a w hData hg Q hQ
  let E : Set ((ℝ × (R3 × ℝ)) × R3) :=
    {v | n v = (referenceGaugeNormalCoefficient g L Φ a v)⁻¹}
  let V : Set ((ℝ × (R3 × ℝ)) × R3) := interior E
  let U0 : Set (ℝ × (R3 × ℝ)) := {p | ∀ z ∈ sphere (0 : R3) 1, (p,z) ∈ V}
  let U := interior U0
  have hQCover (p : ℝ × (R3 × ℝ)) (hp : p ∈ Q) (z : R3) (hz : z ∈ sphere (0 : R3) 1) :
      (p,z) ∈ V := mem_interior_iff_mem_nhds.mpr (hNear (p,z) ⟨hp,hz⟩)
  have hUniform (p : ℝ × (R3 × ℝ)) (hp : p ∈ Q) :
      ∀ᶠ u in 𝓝 p, ∀ z ∈ sphere (0 : R3) 1, (u,z) ∈ V := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact isOpen_interior.mem_nhds (hQCover p hp z hz)
  have hQU : Q ⊆ U := by
    intro p hp
    exact mem_interior_iff_mem_nhds.mpr (hUniform p hp)
  let K : Set R3 := Prod.snd '' tsupport n
  have hK : IsCompact K := hnc.image continuous_snd
  have hz : ∀ p z, z ∉ K → n (p,z) = 0 := by
    intro p z hOut
    by_contra hNZ
    exact hOut ⟨(p,z),subset_tsupport n hNZ,rfl⟩
  refine ⟨⟨n,hn,hnc,K,hK,hz,U,isOpen_interior,hQU,?_⟩⟩
  intro p hp x
  have hxV : (p,x.val) ∈ V := (interior_subset hp) x.val x.property
  exact mem_interior_iff_mem_nhds.mp hxV

def referenceGaugeNormalReciprocalRoomOfCompact
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ReferenceGaugeNormalReciprocalRoom g L Φ a Q :=
  Classical.choice (nonempty_referenceGaugeNormalReciprocalRoom
    g L Φ y0 B ε C ρ H a w hData hg Q hQ)

end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier
variable {g : MatrixField} {L : ℝ}
  {Φ : ℝ → (R3 × R3) → ℝ → R3 × R3}
  {a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ}
  {Q : Set (ℝ × (R3 × ℝ))}

def jets (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q) (n : ℕ) :
    (ℝ × (R3 × ℝ)) → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n R.scalar R.smooth R.spatialSupport R.supportCompact R.zeroOutside

lemma coefficientValue_jets (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (n : ℕ) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue n (R.jets n p) z = R.scalar (p,z) :=
  coefficientValue_commonSupportCoefficientFamily n R.scalar R.smooth
    R.spatialSupport R.supportCompact R.zeroOutside p z

lemma jets_spatial_derivatives (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (n : ℕ) (p : ℝ × (R3 × ℝ)) (k : Fin (n+1)) (z : R3) :
    (R.jets n p).1 k z = iteratedFDeriv ℝ k.val (fun x => R.scalar (p,x)) z :=
  commonSupportCoefficientFamily_jet n R.scalar R.smooth
    R.spatialSupport R.supportCompact R.zeroOutside p k z

lemma contDiff_jets_val (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => (R.jets n p).1) :=
  contDiff_commonSupportCoefficientFamily_val n R.scalar R.smooth
    R.spatialSupport R.supportCompact R.zeroOutside

lemma sphere_value (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ R.parameterRoom) (x : UnitSphere) :
    R.scalar (p,x.val) = (referenceGaugeNormalCoefficient g L Φ a (p,x.val))⁻¹ :=
  by
    have hNear : R.scalar =ᶠ[𝓝 (p,x.val)]
        (fun v => (referenceGaugeNormalCoefficient g L Φ a v)⁻¹) := R.near_eq p hp x
    exact hNear.self_of_nhds

def halfMultiplier (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0 (R.jets 2 p)

def negativeMultiplier (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (R.jets 2 p)

def threeHalfMultiplier (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (R.jets 3 p)

variable (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma high_half_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (R.threeHalfMultiplier hcalc hF hO hD τ0 p) =
    (R.halfMultiplier hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) :=
  nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 (R.jets 3 p) (R.jets 2 p) (by
    funext z
    rw [R.coefficientValue_jets,R.coefficientValue_jets])

lemma half_negative_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (R.halfMultiplier hcalc hF hO hD τ0 p) =
    (R.negativeMultiplier hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) :=
  nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (R.jets 2 p)

lemma contDiff_halfMultiplier : ContDiff ℝ ∞ (R.halfMultiplier hcalc hF hO hD τ0) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 R.scalar R.smooth
    R.spatialSupport R.supportCompact R.zeroOutside

lemma contDiff_negativeMultiplier : ContDiff ℝ ∞ (R.negativeMultiplier hcalc hF hO hD τ0) :=
  contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 R.scalar R.smooth
    R.spatialSupport R.supportCompact R.zeroOutside

lemma contDiff_threeHalfMultiplier : ContDiff ℝ ∞ (R.threeHalfMultiplier hcalc hF hO hD τ0) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 R.scalar R.smooth
    R.spatialSupport R.supportCompact R.zeroOutside

lemma exists_compact_jets_val_bounds (n : ℕ)
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (fun t => (R.jets n t).1) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _ (R.contDiff_jets_val n) K hK N

lemma exists_compact_halfMultiplier_bounds
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (R.halfMultiplier hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _ (R.contDiff_halfMultiplier hcalc hF hO hD τ0) K hK N

lemma exists_compact_negativeMultiplier_bounds
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (R.negativeMultiplier hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _ (R.contDiff_negativeMultiplier hcalc hF hO hD τ0) K hK N

lemma exists_compact_threeHalfMultiplier_bounds
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (R.threeHalfMultiplier hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _ (R.contDiff_threeHalfMultiplier hcalc hF hO hD τ0) K hK N

end OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom

namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (y0 : R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)


lemma referenceGaugeNormalReciprocalRoom_native_inverse_graph
    {Q : Set (ℝ × (R3 × ℝ))} (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ R.parameterRoom) :
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse =
      R.halfMultiplier hcalc hF hO hD τ0 p ∧
    (referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse =
      R.negativeMultiplier hcalc hF hO hD τ0 p := by
  have hValue : ∀ x : UnitSphere, coefficientValue 2 (R.jets 2 p) x.val =
      (referenceGaugeNormalCoefficient g L Φ a (p,x.val))⁻¹ := by
    intro x
    exact (R.coefficientValue_jets 2 p x.val).trans (R.sphere_value p hp x)
  exact ⟨referenceGaugeNormalHalfMultiplier_inverse_eq_native_reciprocal
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p (R.jets 2 p) hValue,
    referenceGaugeNormalNegativeMultiplier_inverse_eq_native_reciprocal
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p (R.jets 2 p) hValue⟩

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom
#print axioms OAI.AnisotropicCalderon.ConnectionError.nonempty_referenceGaugeNormalReciprocalRoom
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalReciprocalRoomOfCompact
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.jets
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.coefficientValue_jets
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.jets_spatial_derivatives
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.contDiff_jets_val
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.sphere_value
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.halfMultiplier
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.negativeMultiplier
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.threeHalfMultiplier
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.high_half_compatibility
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.half_negative_compatibility
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.contDiff_halfMultiplier
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.contDiff_negativeMultiplier
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.contDiff_threeHalfMultiplier
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.exists_compact_jets_val_bounds
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.exists_compact_halfMultiplier_bounds
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.exists_compact_negativeMultiplier_bounds
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.exists_compact_threeHalfMultiplier_bounds
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalReciprocalRoom_native_inverse_graph
