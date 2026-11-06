import Calderon.PhysicalDegreeCasimirCompatibilitySpace
import Calderon.FiniteHarmonicDegreeNormalizedDirectionLift
import Calderon.FinitePhysicalCasimirOperatorAssembly
import Calderon.PhysicalDegreeCasimirCompatibleNormedStructure
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic SmoothSphereRotationProjection RotationCasimirEstimate SpectralSylvester
/-! Full upfront EXPANSION-v001.json. Concrete finite estimates from the original
closed constraints. Actual chosen-family norm infinity remains separate. -/

def compatibleDegreeSharpBlockL
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (m n : ℕ) :
    harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
  (sphereSobolevCoefficientL (1/2:ℝ) m).comp
    (x.1.1.2.comp (sphereSobolevSingleL (3/2:ℝ) n))

lemma compatibleDegreeSharpBlockL_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (m n : ℕ)
    (u : harmonicSphereSubspace n) :
    compatibleDegreeSharpBlockL hO hD x m n u =
      sphereSobolevCoefficientL (1/2:ℝ) m
        (x.1.1.2 (sphereSobolevSingleL (3/2:ℝ) n u)) := rfl

lemma norm_compatibleDegree_primal_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (ij : Fin 3 × Fin 3) :
    ‖x.1.2.1 ij‖ ≤ ‖x‖ :=
  (norm_le_pi_norm x.1.2.1 ij).trans ((norm_fst_le x.1.2).trans (norm_snd_le x.1))

lemma norm_compatibleDegree_adjoint_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (ij : Fin 3 × Fin 3) :
    ‖x.1.2.2 ij‖ ≤ ‖x‖ :=
  (norm_le_pi_norm x.1.2.2 ij).trans ((norm_snd_le x.1.2).trans (norm_snd_le x.1))

lemma compatibleDegree_probability_adjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD)
    (ij : Fin 3 × Fin 3) (f g : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm (x.1.2.1 ij f),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) g)⟫_ℝ =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) f),
      (sphereSobolevZeroEquiv hO hD).symm (x.1.2.2 ij g)⟫_ℝ := by
  have hValue := degreeAdjointScalarL_apply hO hD ij f g x.1
  have hZero := physicalDegreeCasimirCompatibleData_adjoint hO hD x ij f g
  exact sub_eq_zero.mp (hValue.symm.trans hZero)

lemma compatibleDegree_finite_casimir_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD)
    (ncut mcut : ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    |∑ m ∈ Finset.range mcut, ∑ n ∈ Finset.range ncut,
      (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*
        ⟪compatibleDegreeSharpBlockL hO hD x m n (u n),v m⟫_ℝ)| ≤
      (6*Real.sqrt 2*‖x‖) *
        Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ)*((k:ℝ)+1))*‖u k‖^2) *
        Real.sqrt (∑ k ∈ Finset.range mcut, (1+(k:ℝ)*((k:ℝ)+1))*‖v k‖^2) := by
  have hValue := degreeFiniteCasimirScalarL_apply hO hD ncut mcut u v x.1
  have hZero := physicalDegreeCasimirCompatibleData_casimir hO hD x ncut mcut u v
  have hIdentity := sub_eq_zero.mp (hValue.symm.trans hZero)
  have hEstimate := finite_physical_casimir_pairing_le_of_adjoint_operator_bounds
    hO hD x.1.2.1 x.1.2.2 ‖x‖ ‖x‖ (norm_nonneg x) (norm_nonneg x)
    (norm_compatibleDegree_primal_le hO hD x) (norm_compatibleDegree_adjoint_le hO hD x)
    (compatibleDegree_probability_adjoint hO hD x) ncut mcut u v
  change (∑ m ∈ Finset.range mcut, ∑ n ∈ Finset.range ncut,
    (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*
      ⟪compatibleDegreeSharpBlockL hO hD x m n (u n),v m⟫_ℝ)) = _ at hIdentity
  calc
    _ ≤ (3*Real.sqrt 2*(‖x‖+‖x‖)) *
        Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ)*((k:ℝ)+1))*‖u k‖^2) *
        Real.sqrt (∑ k ∈ Finset.range mcut, (1+(k:ℝ)*((k:ℝ)+1))*‖v k‖^2) :=
      (congrArg abs hIdentity).trans_le hEstimate
    _ = _ := by ring

lemma compatibleDegree_finite_degree_half_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD)
    (ncut : ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    |∑ m ∈ Finset.range ncut, ∑ n ∈ Finset.range ncut,
      ((m:ℝ)-(n:ℝ))*⟪compatibleDegreeSharpBlockL hO hD x m n (u n),v m⟫_ℝ| ≤
      (12*Real.sqrt 2*‖x‖) *
        Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ))*‖u k‖^2) *
        Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ))*‖v k‖^2) := by
  have h := finite_harmonic_degree_half_form_bound_of_casimir_product_bound
    (Finset.range ncut) (compatibleDegreeSharpBlockL hO hD x)
    (6*Real.sqrt 2*‖x‖) (by positivity)
    (compatibleDegree_finite_casimir_bound hO hD x ncut ncut) u v
  calc
    _ ≤ 2*(6*Real.sqrt 2*‖x‖) *
        Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ))*‖u k‖^2) *
        Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ))*‖v k‖^2) := h
    _ = _ := by ring

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeSharpBlockL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeSharpBlockL_apply
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.norm_compatibleDegree_primal_le
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.norm_compatibleDegree_adjoint_le
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegree_probability_adjoint
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegree_finite_casimir_bound
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegree_finite_degree_half_bound
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
